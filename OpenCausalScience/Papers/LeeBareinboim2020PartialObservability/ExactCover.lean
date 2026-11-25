module
public import Std

/-! # Exact cover of identified factors

Lee and Bareinboim, corrected R-58 (2026-10-25), §4.2 and Algorithm 1
line 13. The input is the list of candidate subsets of the factor indices.
Each candidate may be used once. The table stores a witness for every
reachable subset. The work count is in table-cell updates, where a mask
operation and an indexed lookup count as one operation each.

Source: https://www.sanghacklee.me/ai-corrected/R58_AI_corrected_2026-10-25.pdf
-/

namespace OpenCausalScience.Papers.LeeBareinboim2020PartialObservability.ExactCover

@[expose] public section

variable {n : Nat}

/-- An ordered selection of pairwise disjoint pieces with the stated union.
The selection respects the multiplicities of the given list. -/
inductive Cover : List (BitVec n) → List (BitVec n) → BitVec n → Prop where
  | empty : Cover [] [] 0
  | skip {pieces use : List (BitVec n)} {target : BitVec n} (piece : BitVec n) :
      Cover pieces use target → Cover (piece :: pieces) use target
  | take {pieces use : List (BitVec n)} {target : BitVec n} (piece : BitVec n) :
      Cover pieces use target → piece &&& target = 0 →
      Cover (piece :: pieces) (piece :: use) (piece ||| target)

abbrev Row (n : Nat) := Vector (Option (List (BitVec n))) (2 ^ n)

structure SearchTable (n : Nat) where
  row : Row n
  updates : Nat

def lookup (row : Row n) (target : BitVec n) : Option (List (BitVec n)) :=
  row[target.toFin.val]

def initial (n : Nat) : Row n :=
  Vector.ofFn fun i => if BitVec.ofFin i = (0 : BitVec n) then some [] else none

/-- Try omitting the new piece. If that fails, the piece must lie inside
the target. Remove exactly its bits and look up the residual. -/
def updateCell (piece : BitVec n) (row : Row n) (target : BitVec n) :
    Option (List (BitVec n)) :=
  match lookup row target with
  | some use => some use
  | none =>
    if piece &&& target = piece then
      (lookup row (target ^^^ piece)).map (List.cons piece)
    else none

def update (piece : BitVec n) (row : Row n) : Row n :=
  Vector.ofFn fun i => updateCell piece row (BitVec.ofFin i)

/-- Each candidate tabulates every subset exactly once. -/
def tabulate : List (BitVec n) → SearchTable n
  | [] => ⟨initial n, 0⟩
  | piece :: tail =>
    let previous := tabulate tail
    let next := update piece previous.row
    ⟨next, previous.updates + next.toArray.size⟩

def solve (pieces : List (BitVec n)) (target : BitVec n) : Option (List (BitVec n)) :=
  lookup (tabulate pieces).row target

@[simp] theorem lookup_initial (target : BitVec n) :
    lookup (initial n) target = if target = 0 then some [] else none := by
  simp only [lookup, initial, Vector.getElem_ofFn]

@[simp] theorem lookup_update (piece : BitVec n) (row : Row n) (target : BitVec n) :
    lookup (update piece row) target = updateCell piece row target := by
  simp only [lookup, update, Vector.getElem_ofFn]

theorem solve_empty (target : BitVec n) :
    solve [] target = if target = 0 then some [] else none := by
  simp [solve, tabulate]

theorem solve_cons (piece : BitVec n) (pieces : List (BitVec n)) (target : BitVec n) :
    solve (piece :: pieces) target =
      match solve pieces target with
      | some use => some use
      | none =>
        if piece &&& target = piece then
          (solve pieces (target ^^^ piece)).map (List.cons piece)
        else none := by
  simp [solve, tabulate, updateCell]

private theorem contained_in_union (piece rest : BitVec n) :
    piece &&& (piece ||| rest) = piece := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases piece.getLsbD i <;> simp

private theorem residual_of_disjoint {piece rest : BitVec n} (disjoint : piece &&& rest = 0) :
    (piece ||| rest) ^^^ piece = rest := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have bits := congrArg (fun mask : BitVec n => mask.getLsbD i) disjoint
  change (piece &&& rest).getLsbD i = (0 : BitVec n).getLsbD i at bits
  simp only [BitVec.getLsbD_and] at bits
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or]
  cases hp : piece.getLsbD i <;> cases hr : rest.getLsbD i <;>
    simp [hp, hr] at bits ⊢

private theorem disjoint_residual {piece target : BitVec n} (contained : piece &&& target = piece) :
    piece &&& (target ^^^ piece) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have bits := congrArg (fun mask : BitVec n => mask.getLsbD i) contained
  change (piece &&& target).getLsbD i = piece.getLsbD i at bits
  simp only [BitVec.getLsbD_and] at bits
  change (piece &&& (target ^^^ piece)).getLsbD i = (0 : BitVec n).getLsbD i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases hp : piece.getLsbD i <;> cases ht : target.getLsbD i <;>
    simp [hp, ht] at bits ⊢

private theorem union_residual {piece target : BitVec n} (contained : piece &&& target = piece) :
    piece ||| (target ^^^ piece) = target := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have bits := congrArg (fun mask : BitVec n => mask.getLsbD i) contained
  change (piece &&& target).getLsbD i = piece.getLsbD i at bits
  simp only [BitVec.getLsbD_and] at bits
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or]
  cases hp : piece.getLsbD i <;> cases ht : target.getLsbD i <;>
    simp [hp, ht] at bits ⊢

/-- Every returned selection covers exactly the requested factors and is
made from the supplied pieces with no factor used twice. -/
theorem solve_sound {pieces use : List (BitVec n)} {target : BitVec n}
    (found : solve pieces target = some use) : Cover pieces use target := by
  induction pieces generalizing use target with
  | nil =>
    rw [solve_empty] at found
    simp at found
    obtain ⟨rfl, rfl⟩ := found
    exact .empty
  | cons piece tail ih =>
    rw [solve_cons] at found
    cases previous : solve tail target with
    | some picked =>
      simp only [previous, Option.some.injEq] at found
      subst use
      exact .skip piece (ih previous)
    | none =>
      by_cases contained : piece &&& target = piece
      · cases residual : solve tail (target ^^^ piece) with
        | none => simp [previous, contained, residual] at found
        | some picked =>
          simp [previous, contained, residual] at found
          subst use
          rw [← union_residual contained]
          exact .take piece (ih residual) (disjoint_residual contained)
      · simp [previous, contained] at found

theorem solve_complete {pieces use : List (BitVec n)} {target : BitVec n}
    (valid : Cover pieces use target) : ∃ found, solve pieces target = some found := by
  induction valid with
  | empty => exact ⟨[], by simp [solve_empty]⟩
  | skip piece _ ih =>
    obtain ⟨found, eq⟩ := ih
    exact ⟨found, by simp [solve_cons, eq]⟩
  | @take tail picked rest piece _ disjoint ih =>
    obtain ⟨found, eq⟩ := ih
    cases previous : solve tail (piece ||| rest) with
    | some other => exact ⟨other, by simp [solve_cons, previous]⟩
    | none =>
      refine ⟨piece :: found, ?_⟩
      simp [solve_cons, previous, contained_in_union, residual_of_disjoint disjoint, eq]

theorem solve_succeeds_iff (pieces : List (BitVec n)) (target : BitVec n) :
    (∃ found, solve pieces target = some found) ↔ ∃ use, Cover pieces use target := by
  constructor
  · rintro ⟨found, eq⟩
    exact ⟨found, solve_sound eq⟩
  · rintro ⟨_, valid⟩
    exact solve_complete valid

/-- The phase-two DP updates one row of 2ⁿ cells per candidate. Initializing
the empty-candidate row costs one additional row. -/
theorem tabulate_updates (pieces : List (BitVec n)) :
    (tabulate pieces).updates = pieces.length * 2 ^ n := by
  induction pieces with
  | nil => simp [tabulate]
  | cons piece tail ih => simp [tabulate, ih, Nat.succ_mul]

/-- The number of candidate entries is bounded by the factor count times
the number of supplied distributions when each distribution contributes
at most one candidate per factor. -/
theorem candidate_count {α : Type} (perDistribution : List (List α)) (factors : Nat)
    (oneEach : ∀ entries ∈ perDistribution, entries.length ≤ factors) :
    perDistribution.flatten.length ≤ perDistribution.length * factors := by
  induction perDistribution with
  | nil => simp
  | cons entries rest ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.succ_mul]
    rw [Nat.add_comm (rest.length * factors) factors]
    exact Nat.add_le_add (oneEach entries List.mem_cons_self)
      (ih fun xs mem => oneEach xs (List.mem_cons_of_mem entries mem))

end

end OpenCausalScience.Papers.LeeBareinboim2020PartialObservability.ExactCover

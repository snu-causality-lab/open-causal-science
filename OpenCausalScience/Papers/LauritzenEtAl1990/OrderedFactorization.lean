module
public import OpenCausalScience.Graph.DAG
public import OpenCausalScience.Probability.ConditionalIndependence

/-! # Directed local Markov property and recursive factorization

The finite-cell form of the directed local Markov property uses cross
products in each parent cell. Under a topological labelling it gives
the observational recursive factorization on the full assignment,
including parent cells of mass zero. Source:
https://doi.org/10.1002/net.3230200503
-/

namespace OpenCausalScience.Papers.LauritzenEtAl1990.OrderedFactorization

open Probability (FiniteLaw)
open Probability.FiniteMass (mass)

@[expose] public section

variable {n : Nat} {A : Type} [DecidableEq A]

abbrev Assignment (n : Nat) (A : Type) := Fin n → A

def prefixEvent (count : Nat) (x sample : Assignment n A) : Bool :=
  (List.finRange n).all fun v => decide (v.val < count → sample v = x v)

def parents (G : DAG n) (v : Fin n) (x sample : Assignment n A) : Bool :=
  (List.finRange n).all fun u => decide (G.edge u v = true → sample u = x u)

def atVertex (v : Fin n) (x sample : Assignment n A) : Bool :=
  decide (sample v = x v)

theorem prefix_iff (count : Nat) (x sample : Assignment n A) :
    prefixEvent count x sample = true ↔ ∀ v : Fin n, v.val < count → sample v = x v := by
  simp only [prefixEvent, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

theorem parents_iff (G : DAG n) (v : Fin n) (x sample : Assignment n A) :
    parents G v x sample = true ↔ ∀ u : Fin n, G.edge u v = true → sample u = x u := by
  simp only [parents, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

theorem prefix_step (v : Fin n) (x : Assignment n A) :
    prefixEvent (v.val + 1) x = fun sample => prefixEvent v.val x sample && atVertex v x sample := by
  funext sample
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true, prefix_iff, prefix_iff]
  simp only [atVertex, decide_eq_true_eq]
  constructor
  · intro agree
    exact ⟨fun u earlier => agree u (by omega), agree v (by omega)⟩
  · rintro ⟨earlier, current⟩ u bound
    by_cases same : u = v
    · exact same ▸ current
    · have neq : u.val ≠ v.val := fun h => same (Fin.ext h)
      exact earlier u (by omega)

theorem prefix_implies_parents (G : DAG n)
    (topological : ∀ u v, G.edge u v = true → u < v)
    (v : Fin n) (x sample : Assignment n A) (matched : prefixEvent v.val x sample = true) :
    parents G v x sample = true :=
  (parents_iff G v x sample).mpr fun u edge =>
    (prefix_iff v.val x sample).mp matched u (topological u v edge)

theorem local_cell_most_recent (G : DAG n) (atoms : List (Assignment n A))
    (weight : Assignment n A → Rat) (x : Assignment n A) (v : Fin n)
    (topological : ∀ u v, G.edge u v = true → u < v)
    (localCell :
      mass atoms weight (fun s => (prefixEvent v.val x s && atVertex v x s) && parents G v x s) *
        mass atoms weight (parents G v x) =
      mass atoms weight (fun s => prefixEvent v.val x s && parents G v x s) *
        mass atoms weight (fun s => atVertex v x s && parents G v x s)) :
    mass atoms weight (prefixEvent (v.val + 1) x) * mass atoms weight (parents G v x) =
      mass atoms weight (prefixEvent v.val x) *
        mass atoms weight (fun s => atVertex v x s && parents G v x s) := by
  have keepPrefix : (fun s => prefixEvent v.val x s && parents G v x s) = prefixEvent v.val x := by
    funext s
    cases hp : prefixEvent v.val x s
    · simp
    · simp [prefix_implies_parents G topological v x s hp]
  have keepBoth : (fun s => (prefixEvent v.val x s && atVertex v x s) && parents G v x s) =
      (fun s => prefixEvent v.val x s && atVertex v x s) := by
    funext s
    cases hp : prefixEvent v.val x s
    · simp
    · simp [prefix_implies_parents G topological v x s hp]
  rw [keepPrefix, keepBoth] at localCell
  simpa only [prefix_step] using localCell

def conditionalFactor (G : DAG n) (atoms : List (Assignment n A))
    (weight : Assignment n A → Rat) (default : A) (x : Assignment n A) (v : Fin n) : Rat :=
  let evidence := mass atoms weight (parents G v x)
  if evidence = 0 then (if x v = default then 1 else 0)
  else mass atoms weight (fun s => atVertex v x s && parents G v x s) / evidence

def prefixProduct (factor : Fin n → Rat) : (count : Nat) → count ≤ n → Rat
  | 0, _ => 1
  | k + 1, within => prefixProduct factor k (by omega) * factor ⟨k, by omega⟩

theorem recursive_factorization
    (G : DAG n) (atoms : List (Assignment n A)) (weight : Assignment n A → Rat)
    (default : A) (x : Assignment n A)
    (normalized : mass atoms weight (fun _ => true) = 1)
    (localCells : ∀ v : Fin n,
      mass atoms weight (prefixEvent (v.val + 1) x) * mass atoms weight (parents G v x) =
      mass atoms weight (prefixEvent v.val x) *
        mass atoms weight (fun s => atVertex v x s && parents G v x s))
    (zeroParent : ∀ v : Fin n, mass atoms weight (parents G v x) = 0 →
      mass atoms weight (prefixEvent v.val x) = 0 ∧ mass atoms weight (prefixEvent (v.val + 1) x) = 0) :
    ∀ k (within : k ≤ n),
      mass atoms weight (prefixEvent k x) =
        prefixProduct (conditionalFactor G atoms weight default x) k within := by
  intro k
  induction k with
  | zero =>
    intro within
    have empty : prefixEvent 0 x = fun _ => true := by
      funext s
      exact (prefix_iff 0 x s).mpr (by omega)
    rw [empty, normalized]
    rfl
  | succ k ih =>
    intro within
    let v : Fin n := ⟨k, by omega⟩
    have prior := ih (show k ≤ n by omega)
    change mass atoms weight (prefixEvent (v.val + 1) x) =
      prefixProduct (conditionalFactor G atoms weight default x) k (by omega) *
        conditionalFactor G atoms weight default x v
    rw [← prior]
    unfold conditionalFactor
    by_cases zero : mass atoms weight (parents G v x) = 0
    · rw [(zeroParent v zero).1, (zeroParent v zero).2, Rat.zero_mul]
    · simp only [zero, ite_false]
      have cell := congrArg (· / mass atoms weight (parents G v x)) (localCells v)
      rw [Rat.mul_div_cancel zero] at cell
      simpa only [Rat.div_def, Rat.mul_assoc] using cell

theorem full_prefix_iff (x sample : Assignment n A) :
    prefixEvent n x sample = true ↔ sample = x := by
  rw [prefix_iff]
  exact ⟨fun h => funext fun v => h v v.isLt, fun h v _ => congrFun h v⟩

def earlierValues (v : Fin n) (sample : Assignment n A) : Fin n → Option A :=
  fun u => if u < v then some (sample u) else none

/-- Ordered local Markov property with predecessors read at a fixed
parent cell. The parent coordinates in the predecessor vector are
constant on this cell. -/
def OrderedLocal (G : DAG n) (law : FiniteLaw (Assignment n A)) : Prop :=
  ∀ v x, law.IndependentAt (· v) (earlierValues v) (parents G v x)

open Classical in
theorem earlier_values_event (v : Fin n) (x : Assignment n A) :
    (fun s => decide (earlierValues v s = earlierValues v x)) = prefixEvent v.val x := by
  funext s
  apply Bool.eq_iff_iff.mpr
  simp only [prefix_iff, decide_eq_true_eq]
  constructor
  · intro equal u before
    have same := congrFun equal u
    simpa [earlierValues, (show u < v from before)] using same
  · intro equal
    funext u
    by_cases before : u < v
    · simp [earlierValues, before, equal u before]
    · simp [earlierValues, before]

open Classical in
theorem ordered_local_factorization (G : DAG n) (law : FiniteLaw (Assignment n A))
    (normalized : law.mass (fun _ => true) = 1)
    (topological : ∀ u v, G.edge u v = true → u < v)
    (localMarkov : OrderedLocal G law) (default : A) (x : Assignment n A) :
    law.mass (fun sample => decide (sample = x)) =
      prefixProduct (conditionalFactor G law.atoms law.weight default x) n (by omega) := by
  have full : (fun sample => decide (sample = x)) = prefixEvent n x := by
    funext sample
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using (full_prefix_iff x sample).symm
  rw [full]
  apply recursive_factorization G law.atoms law.weight default x normalized
  · intro v
    apply local_cell_most_recent G law.atoms law.weight x v topological
    have cell := localMarkov v x (fun a => decide (a = x v))
      (fun a => decide (a = earlierValues v x))
    change law.mass (FiniteLaw.andEvent (parents G v x)
        (FiniteLaw.andEvent (atVertex v x) (fun s => decide (earlierValues v s = earlierValues v x)))) *
        law.mass (parents G v x) =
      law.mass (FiniteLaw.andEvent (parents G v x) (atVertex v x)) *
        law.mass (FiniteLaw.andEvent (parents G v x)
          (fun s => decide (earlierValues v s = earlierValues v x))) at cell
    rw [earlier_values_event] at cell
    change mass law.atoms law.weight
        (fun s => parents G v x s && (atVertex v x s && prefixEvent v.val x s)) *
          mass law.atoms law.weight (parents G v x) =
        mass law.atoms law.weight (fun s => parents G v x s && atVertex v x s) *
          mass law.atoms law.weight (fun s => parents G v x s && prefixEvent v.val x s) at cell
    simpa only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm, Rat.mul_comm] using cell
  · intro v zero
    refine ⟨law.submass_eq_zero (fun s _ h => prefix_implies_parents G topological v x s h) zero, ?_⟩
    apply law.submass_eq_zero _ zero
    intro s _ h
    rw [prefix_step] at h
    exact prefix_implies_parents G topological v x s (Bool.and_eq_true_iff.mp h).1

end
end OpenCausalScience.Papers.LauritzenEtAl1990.OrderedFactorization

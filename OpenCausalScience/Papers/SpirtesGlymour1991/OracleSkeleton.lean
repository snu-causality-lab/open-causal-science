module
public import OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

/-! The adjacency-union version of the oracle PC search in Spirtes and
Glymour (1991), pages 67–70, with recorded separators as in the appendix.
This reference search freezes the graph within each cardinality round. -/

namespace OpenCausalScience.Papers.SpirtesGlymour1991.OracleSkeleton

open OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat}

abbrev Oracle (n : Nat) := Fin n → Fin n → (Fin n → Bool) → Bool

/-- The oracle agrees with graphical separation on disjoint queries. -/
def Exact (G : DAG n) (oracle : Oracle n) : Prop :=
  ∀ x y conditioned, x ≠ y → conditioned x = false → conditioned y = false →
    (oracle x y conditioned = true ↔ ¬ DConnected (Conditioning.ofPredicate G conditioned) x y)

/-- For distinct vertices, an absent separator indicates a remaining edge. -/
abbrev Separators (n : Nat) := Fin n → Fin n → Option (List (Fin n))

def live (state : Separators n) (x y : Fin n) : Bool :=
  (x != y) && (state x y).isNone

def eligible (state : Separators n) (x y v : Fin n) : Bool :=
  (v != x) && (v != y) && (live state x v || live state y v)

def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: rest => subsets rest ++ (subsets rest).map (a :: ·)

private theorem filter_mem_subsets {α : Type} (p : α → Bool) (xs : List α) :
    xs.filter p ∈ subsets xs := by
  induction xs with
  | nil => simp [subsets]
  | cons a xs ih =>
    cases h : p a with
    | false => simp [subsets, h, ih]
    | true =>
      rw [List.filter_cons, ite_eq_left h, subsets, List.mem_append]
      exact Or.inr (List.mem_map_of_mem ih)

def candidate (oracle : Oracle n) (state : Separators n)
    (size : Nat) (x y : Fin n) (zs : List (Fin n)) : Bool :=
  (zs.length == size) && zs.all (eligible state x y) &&
    (oracle x y (zs.contains ·) || oracle y x (zs.contains ·))

def findSeparator (oracle : Oracle n) (state : Separators n)
    (size : Nat) (x y : Fin n) : Option (List (Fin n)) :=
  (subsets (List.finRange n)).find? (candidate oracle state size x y)

def run (oracle : Oracle n) : Nat → Separators n
  | 0 => fun _ _ => none
  | size + 1 => fun x y =>
      (run oracle size x y).or (findSeparator oracle (run oracle size) size x y)

private theorem candidate_valid {oracle : Oracle n} {state : Separators n}
    {size : Nat} {x y : Fin n} {zs : List (Fin n)}
    (found : candidate oracle state size x y zs = true) :
    zs.contains x = false ∧ zs.contains y = false ∧
      (oracle x y (zs.contains ·) = true ∨ oracle y x (zs.contains ·) = true) := by
  simp only [candidate, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at found
  have outside (z : Fin n) (eq : z = x ∨ z = y) : zs.contains z = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    have check := found.1.2 z (List.contains_iff_mem.mp present)
    rcases eq with rfl | rfl <;> simp [eligible] at check
  exact ⟨outside x (.inl rfl), outside y (.inr rfl), found.2⟩

/-- The saved separator is disjoint from the endpoints and separates them. -/
theorem saved_separator {G : DAG n} {oracle : Oracle n} (exactOracle : Exact G oracle)
    (size : Nat) {x y : Fin n} (distinct : x ≠ y) {zs : List (Fin n)}
    (found : run oracle size x y = some zs) :
    zs.contains x = false ∧ zs.contains y = false ∧
      (¬ DConnected (Conditioning.ofPredicate G (zs.contains ·)) x y ∨
       ¬ DConnected (Conditioning.ofPredicate G (zs.contains ·)) y x) := by
  induction size with
  | zero => simp [run] at found
  | succ size ih =>
    change (run oracle size x y).or
      (findSeparator oracle (run oracle size) size x y) = some zs at found
    cases saved : run oracle size x y with
    | some earlier =>
      rw [saved] at found
      have same : earlier = zs := Option.some.inj found
      exact ih (saved.trans (congrArg some same))
    | none =>
      rw [saved] at found
      have valid := candidate_valid (List.find?_some found)
      refine ⟨valid.1, valid.2.1, ?_⟩
      exact valid.2.2.imp
        ((exactOracle x y _ distinct valid.1 valid.2.1).mp)
        ((exactOracle y x _ distinct.symm valid.2.1 valid.1).mp)

private theorem adjacent_nonloop {G : DAG n} {x y : Fin n}
    (edge : Adjacent G x y) : x ≠ y := by
  rintro rfl
  exact G.no_directed_cycle x (.single (edge.elim id id))

/-- No round deletes a true skeleton edge. -/
theorem live_of_adjacent {G : DAG n} {oracle : Oracle n} (exactOracle : Exact G oracle)
    (size : Nat) {x y : Fin n} (edge : Adjacent G x y) : live (run oracle size) x y = true := by
  have distinct := adjacent_nonloop edge
  cases saved : run oracle size x y with
  | none => simp [live, distinct, saved]
  | some zs =>
    obtain ⟨hx, hy, separated⟩ := saved_separator exactOracle size distinct saved
    exact (separated.elim (fun bad => bad (adjacent_dConnected _ edge hx hy))
      (fun bad => bad (adjacent_dConnected _ (Or.symm edge) hy hx))).elim

private theorem none_at_earlier_round {oracle : Oracle n} {x y : Fin n}
    {early later : Nat} (before : early ≤ later) (still : run oracle later x y = none) :
    run oracle early x y = none := by
  induction later with
  | zero => simpa [Nat.eq_zero_of_le_zero before] using still
  | succ later ih =>
    by_cases final : early = later + 1
    · simpa [final] using still
    · have prior : early ≤ later := by omega
      exact ih prior ((Option.or_eq_none_iff.mp still).1)

private theorem test_parent_set {G : DAG n} {oracle : Oracle n} (exactOracle : Exact G oracle)
    {x y : Fin n} (distinct : x ≠ y) (missing : ¬ Adjacent G x y)
    (sep : ¬ DConnected (parentCondition G x) x y) :
    ∃ k ≤ n, findSeparator oracle (run oracle k) k x y ≠ none ∧
             findSeparator oracle (run oracle k) k y x ≠ none := by
  let zs := (List.finRange n).filter (fun p => G.edge p x)
  let k := zs.length
  have hz (v : Fin n) : zs.contains v = G.edge v x := by
    apply Bool.eq_iff_iff.mpr
    rw [List.contains_iff_mem, List.mem_filter]
    exact ⟨And.right, fun parent => ⟨List.mem_finRange _, parent⟩⟩
  have hx : G.edge x x = false := Bool.eq_false_iff.mpr
    (fun loop => G.no_directed_cycle x (.single loop))
  have hy : G.edge y x = false := Bool.eq_false_iff.mpr (fun parent => missing (Or.inr parent))
  have test : oracle x y (zs.contains ·) = true := by
    have equal : (fun v => zs.contains v) = (fun v => G.edge v x) := funext hz
    rw [equal]
    exact (exactOracle x y (fun v => G.edge v x) distinct hx hy).mpr sep
  have parent_live (v : Fin n) (mem : v ∈ zs) : live (run oracle k) x v = true :=
    live_of_adjacent exactOracle k (Or.inr (List.mem_filter.mp mem).2)
  have avoids (v : Fin n) (mem : v ∈ zs) : v ≠ x ∧ v ≠ y := by
    have parent := (List.mem_filter.mp mem).2
    exact ⟨fun same => by simp [same, hx] at parent,
      fun same => by simp [same, hy] at parent⟩
  have yes : candidate oracle (run oracle k) k x y zs = true := by
    simp only [candidate, k, beq_self_eq_true, Bool.true_and, test, Bool.true_or, Bool.and_true]
    exact List.all_eq_true.mpr fun v mem => by
      obtain ⟨ax, ay⟩ := avoids v mem
      simp [eligible, ax, ay, show live (run oracle zs.length) x v = true from parent_live v mem]
  have swapped : candidate oracle (run oracle k) k y x zs = true := by
    simp only [candidate, k, beq_self_eq_true, Bool.true_and, test, Bool.or_true, Bool.and_true]
    exact List.all_eq_true.mpr fun v mem => by
      obtain ⟨ax, ay⟩ := avoids v mem
      simp [eligible, ax, ay, show live (run oracle zs.length) x v = true from parent_live v mem]
  have present := filter_mem_subsets (fun v => G.edge v x) (List.finRange n)
  exact ⟨k, by simpa [k, zs] using List.length_filter_le (fun v => G.edge v x) (List.finRange n),
    fun miss => (List.find?_eq_none.mp miss zs present) yes,
    fun miss => (List.find?_eq_none.mp miss zs present) swapped⟩

/-- The bounded adjacency-union search returns exactly the true DAG skeleton. -/
theorem skeleton_iff {G : DAG n} {oracle : Oracle n} (exactOracle : Exact G oracle)
    (x y : Fin n) : live (run oracle (n + 1)) x y = true ↔ Adjacent G x y := by
  refine ⟨?_, live_of_adjacent exactOracle _⟩
  intro present
  have distinct : x ≠ y := by
    intro eq
    simp [live, eq] at present
  have still : run oracle (n + 1) x y = none := by
    simpa [live, distinct, Option.isNone_iff_eq_none] using present
  apply Classical.byContradiction
  intro missing
  rcases nonadjacent_has_separator distinct missing with forward | reverse
  · obtain ⟨k, bound, found, _⟩ := test_parent_set exactOracle distinct missing forward
    have earlier := none_at_earlier_round (Nat.succ_le_succ bound) still
    exact found ((Option.or_eq_none_iff.mp earlier).2)
  · obtain ⟨k, bound, _, found⟩ :=
      test_parent_set exactOracle distinct.symm (fun edge => missing (Or.symm edge)) reverse
    have earlier := none_at_earlier_round (Nat.succ_le_succ bound) still
    exact found ((Option.or_eq_none_iff.mp earlier).2)

/-- On an unshielded triple, the saved separator omits the middle
exactly when the middle is a collider. -/
theorem omitted_middle_iff_collider {G : DAG n} {oracle : Oracle n} (exactOracle : Exact G oracle)
    {x middle y : Fin n} (distinct : x ≠ y)
    (left : live (run oracle (n + 1)) x middle = true)
    (right : live (run oracle (n + 1)) y middle = true)
    {zs : List (Fin n)} (saved : run oracle (n + 1) x y = some zs) :
    zs.contains middle = false ↔ UnshieldedCollider G x middle y := by
  obtain ⟨hx, hy, sep⟩ := saved_separator exactOracle (n + 1) distinct saved
  have leftEdge := (skeleton_iff exactOracle x middle).mp left
  have rightEdge := (skeleton_iff exactOracle y middle).mp right
  have missing : ¬ Adjacent G x y := by
    intro edge
    have h := (skeleton_iff exactOracle x y).mpr edge
    simp [live, saved] at h
  have head : zs.contains middle = false ↔ HeadToHead G x middle y := by
    rcases sep with forward | backward
    · exact middle_omitted_iff_headToHead_of_separating _ leftEdge rightEdge distinct hx hy forward
    · exact (middle_omitted_iff_headToHead_of_separating _ rightEdge leftEdge distinct.symm hy hx
        backward).trans ⟨And.symm, And.symm⟩
  exact head.trans ⟨fun h => ⟨distinct, missing, h⟩, fun h => h.2.2⟩

def bayesBallOracle (G : DAG n) : Oracle n :=
  fun x y conditioned => !(bayesBall G [x] conditioned (fun _ => false)).contains y

/-- The graph-defined oracle can itself be computed by verified Bayes-Ball. -/
theorem bayes_ball_oracle_exact (G : DAG n) : Exact G (bayesBallOracle G) := by
  intro x y conditioned distinct _ _
  have live : (bayesBall G [x] conditioned (fun _ => false)).contains y = true ↔
      DConnected (Conditioning.ofPredicate G conditioned) x y := by
    rw [List.contains_iff_mem, mem_bayesBall_iff]
    simp [Ne.symm distinct]
  cases h : (bayesBall G [x] conditioned (fun _ => false)).contains y with
  | false =>
    simp only [bayesBallOracle, h, Bool.not_false, true_iff]
    exact fun conn => Bool.false_ne_true (h.symm.trans (live.mpr conn))
  | true =>
    simp only [bayesBallOracle, h, Bool.not_true, Bool.false_eq_true, false_iff]
    exact fun denied => denied (live.mp h)

def colliderTest (state : Separators n) (x middle y : Fin n) : Bool :=
  (x != y) && live state x middle && live state y middle &&
    (state x y).any (fun zs => !zs.contains middle)

/-- The executable collider test recovers exactly the unshielded colliders. -/
theorem collider_test_iff {G : DAG n} {oracle : Oracle n} (exactOracle : Exact G oracle)
    (x middle y : Fin n) :
    colliderTest (run oracle (n + 1)) x middle y = true ↔
      UnshieldedCollider G x middle y := by
  by_cases distinct : x = y
  · simp [distinct, colliderTest, UnshieldedCollider]
  have dx : (x != y) = true := by simpa
  cases saved : run oracle (n + 1) x y with
  | none =>
    have still : live (run oracle (n + 1)) x y = true := by simp [live, saved, dx]
    have adj := (skeleton_iff exactOracle x y).mp still
    simp [colliderTest, saved, UnshieldedCollider, adj]
  | some zs =>
    constructor
    · intro test
      have checks : (live (run oracle (n + 1)) x middle = true ∧
          live (run oracle (n + 1)) y middle = true) ∧ zs.contains middle = false := by
        simpa [colliderTest, dx, saved] using test
      exact (omitted_middle_iff_collider exactOracle distinct checks.1.1 checks.1.2 saved).mp
        checks.2
    · intro head
      have left := live_of_adjacent exactOracle (n + 1) (Or.inl head.2.2.1)
      have right := live_of_adjacent exactOracle (n + 1) (Or.inl head.2.2.2)
      have omitted := (omitted_middle_iff_collider exactOracle distinct left right saved).mpr head
      have outside : middle ∉ zs := fun mem =>
        Bool.false_ne_true (omitted.symm.trans (List.contains_iff_mem.mpr mem))
      simp [colliderTest, dx, saved, left, right, outside]

end
end OpenCausalScience.Papers.SpirtesGlymour1991.OracleSkeleton

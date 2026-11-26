module
public import OpenCausalScience.Papers.HauserBuhlmann2012.InterventionalEquivalence

/-! A graph-semantic version of the monotonicity in Ghassami, Salehkaleybar,
Kiyavash and Bareinboim (2018), Lemma 1. A candidate DAG is retained when it
matches the observational signature and the signature after each separate
single-vertex experiment. The count concerns previously unoriented arrows.

The displayed inequality in the main paper runs opposite to the proof in
Supplementary Appendix B. This module proves the latter direction and checks
a two-vertex witness against the printed direction.

* https://proceedings.mlr.press/v80/ghassami18a/ghassami18a.pdf
* https://proceedings.mlr.press/v80/ghassami18a/ghassami18a-supp.pdf
-/

namespace OpenCausalScience.Papers.GhassamiEtAl2018.BudgetedOrientation

open OpenCausalScience.Papers.HauserBuhlmann2012.InterventionalEquivalence
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat}

/-- One observational regime and one distinct experiment for each selected vertex. -/
def regimes (selected : List (Fin n)) : List (Target n) :=
  (fun _ => false) :: selected.map (fun u v => u == v)

private theorem compatible_of_fewer_targets {before after : List (Fin n)}
    (subset : ∀ v ∈ before, v ∈ after) {truth candidate : DAG n}
    (compatible : cutSignaturesMatch (regimes after) truth candidate = true) :
    cutSignaturesMatch (regimes before) truth candidate = true := by
  apply List.all_eq_true.mpr
  intro target member
  apply List.all_eq_true.mp compatible target
  change target ∈ (fun _ => false) :: before.map (fun u v => u == v) at member
  change target ∈ (fun _ => false) :: after.map (fun u v => u == v)
  rcases List.mem_cons.mp member with same | intervention
  · exact List.mem_cons.mpr (.inl same)
  · obtain ⟨v, prior, equ⟩ := List.mem_map.mp intervention
    exact List.mem_cons.mpr (.inr (List.mem_map.mpr ⟨v, subset v prior, equ⟩))

/-- An arrow of the true DAG becomes determined if it was reversible in
the observational class and every candidate still compatible with the
regimes now agrees with its direction. The candidate list supplies the
search universe for this reference calculation. -/
def newlyDetermined (candidates : List (DAG n)) (selected : List (Fin n))
    (truth : DAG n) (u v : Fin n) : Bool :=
  truth.edge u v &&
    (candidates.any (fun candidate => signaturesMatch truth candidate && !candidate.edge u v) &&
    candidates.all (fun candidate =>
      !cutSignaturesMatch (regimes selected) truth candidate || candidate.edge u v))

theorem newly_determined_mono {candidates : List (DAG n)} {before after : List (Fin n)}
    (subset : ∀ v ∈ before, v ∈ after) {truth : DAG n} {u v : Fin n}
    (h : newlyDetermined candidates before truth u v = true) :
    newlyDetermined candidates after truth u v = true := by
  obtain ⟨arrow, reversible, determined⟩ := by
    simpa only [newlyDetermined, Bool.and_eq_true] using h
  apply Bool.and_eq_true_iff.mpr
  refine ⟨arrow, Bool.and_eq_true_iff.mpr ⟨reversible, List.all_eq_true.mpr ?_⟩⟩
  intro candidate member
  cases hAfter : cutSignaturesMatch (regimes after) truth candidate
  · simp
  · have hBefore := compatible_of_fewer_targets subset hAfter
    simpa only [hAfter, hBefore, Bool.not_true, Bool.false_or] using
      List.all_eq_true.mp determined candidate member

/-- The number of newly determined arrows in a fixed true DAG. -/
def directionCount (candidates : List (DAG n)) (selected : List (Fin n)) (truth : DAG n) : Nat :=
  let vertices := List.finRange n
  let pairs := vertices.flatMap fun u => vertices.map fun v => (u, v)
  ((pairs.map fun (u, v) => (newlyDetermined candidates selected truth u v).toNat)).sum

private theorem sum_le_of_pointwise {α : Type} {f g : α → Nat}
    (bound : ∀ x, f x ≤ g x) (values : List α) :
    (values.map f).sum ≤ (values.map g).sum := by
  induction values with
  | nil => exact Nat.le_refl 0
  | cons first rest ih =>
    simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add (bound first) ih

/-- The corrected monotonicity direction for one graph in the class. -/
theorem direction_count_mono (candidates : List (DAG n)) {before after : List (Fin n)}
    (subset : ∀ v ∈ before, v ∈ after) (truth : DAG n) :
    directionCount candidates before truth ≤ directionCount candidates after truth := by
  unfold directionCount
  apply sum_le_of_pointwise
  intro pair
  rcases pair with ⟨u, v⟩
  cases h : newlyDetermined candidates before truth u v
  · simp [h]
  · simp [h, newly_determined_mono subset h]

/-- Sum of the direction counts across candidate true DAGs. A complete
observational class with one entry per edge function gives the numerator
of the corresponding uniform mean, as in equation (1). -/
def directionCountSum (candidates : List (DAG n)) (selected : List (Fin n)) : Nat :=
  (candidates.map (directionCount candidates selected)).sum

theorem direction_count_sum_mono (candidates : List (DAG n)) {before after : List (Fin n)}
    (subset : ∀ v ∈ before, v ∈ after) :
    directionCountSum candidates before ≤ directionCountSum candidates after :=
  sum_le_of_pointwise (direction_count_mono candidates subset) candidates

/-- The two observationally equivalent orientations of a single edge. -/
def forward : DAG 2 where
  edge u v := u == 0 && v == 1
  rank u := u.val
  edge_increases := by decide

def backward : DAG 2 where
  edge u v := u == 1 && v == 0
  rank u := 1 - u.val
  edge_increases := by decide

def oneEdgeClass : List (DAG 2) := [forward, backward]

theorem one_edge_observational_match : signaturesMatch forward backward = true := by decide

theorem one_edge_class_complete (candidate : DAG 2)
    (same : signaturesMatch forward candidate = true) :
    candidate.edge = forward.edge ∨ candidate.edge = backward.edge := by
  have atZero : candidate.edge 0 0 = false := Bool.eq_false_iff.mpr
    (fun edge => candidate.no_directed_cycle 0 (.single edge))
  have atOne : candidate.edge 1 1 = false := Bool.eq_false_iff.mpr
    (fun edge => candidate.no_directed_cycle 1 (.single edge))
  have vertices : ∀ v : Fin 2, v = 0 ∨ v = 1 := by decide
  have adjacent := ((signaturesMatch_iff forward candidate).mp same).1 0 1
  rcases adjacent.mp (.inl rfl) with up | down
  · left
    have notDown : candidate.edge 1 0 = false := Bool.eq_false_iff.mpr
      (fun opposite => candidate.no_directed_cycle 0 (.extend (.single up) opposite))
    funext u v
    rcases vertices u with rfl | rfl <;> rcases vertices v with rfl | rfl
    · exact atZero
    · exact up
    · exact notDown
    · exact atOne
  · right
    have notUp : candidate.edge 0 1 = false := Bool.eq_false_iff.mpr
      (fun opposite => candidate.no_directed_cycle 1 (.extend (.single down) opposite))
    funext u v
    rcases vertices u with rfl | rfl <;> rcases vertices v with rfl | rfl
    · exact atZero
    · exact notUp
    · exact down
    · exact atOne

theorem one_edge_separated_by_intervention :
    cutSignaturesMatch (regimes [0]) forward backward = false := by decide

theorem one_edge_direction_counts :
    directionCountSum oneEdgeClass [] = 0 ∧ directionCountSum oneEdgeClass [0] = 2 := by decide

/-- The two DAGs have uniform scores 0 and 1 before and after adding the
single experiment, so a decreasing direction for D cannot hold. -/
theorem printed_inequality_fails :
    ¬ directionCountSum oneEdgeClass [0] ≤ directionCountSum oneEdgeClass [] := by decide

end
end OpenCausalScience.Papers.GhassamiEtAl2018.BudgetedOrientation

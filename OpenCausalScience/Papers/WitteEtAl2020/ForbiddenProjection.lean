module
public import OpenCausalScience.Papers.HenckelEtAl2022.DAGOSet

/-! # The O-set and forbidden projection

Witte, Henckel, Maathuis and Didelez (2020), Proposition 10. The theorem
compares the O-set in a finite DAG with the outcome parents in its forbidden
projection, excluding treatments and outcomes. We use the directed-edge clause
of the latent projection (Definitions 4–5). No bidirected-edge or adjustment
validity assertion is needed for this equality.

Source: https://jmlr.org/papers/v21/20-175.html.
-/

namespace OpenCausalScience.Papers.WitteEtAl2020.ForbiddenProjection

open OpenCausalScience.Papers.HenckelEtAl2022.DAGOSet

@[expose] public section

variable {n : Nat}

/-- Treatments and outcomes are retained even when forbidden. -/
def Marginalized (graph : DAG n) (treatment outcome : Fin n → Bool) (v : Fin n) : Prop :=
  Forbidden graph treatment outcome v ∧ treatment v = false ∧ outcome v = false

def ProjectedDirectedEdge (graph : DAG n) (treatment outcome : Fin n → Bool)
    (u v : Fin n) : Prop :=
  ¬ Marginalized graph treatment outcome u ∧ ¬ Marginalized graph treatment outcome v ∧
    DirectedPath graph (Marginalized graph treatment outcome) u v

/-- Definition 9, using the directed part of Definition 4. -/
def ProjectedOSet (graph : DAG n) (treatment outcome : Fin n → Bool) (v : Fin n) : Prop :=
  treatment v = false ∧ outcome v = false ∧
    ∃ y, outcome y = true ∧ ProjectedDirectedEdge graph treatment outcome v y

private theorem walk_to_next {graph : DAG n} {treatment : Fin n → Bool} {u v : Fin n}
    (edge : graph.edge u v = true) (reach : TreatmentAncestor graph treatment u) :
    TreatmentAncestor graph treatment v := by
  obtain ⟨a, isTreatment, walk⟩ := reach
  exact ⟨a, isTreatment, .extend walk edge⟩

private theorem projected_path_to_first_outcome {graph : DAG n}
    {treatment outcome : Fin n → Bool} {u y : Fin n}
    (path : DirectedPath graph (fun v => treatment v = false) u y) (endOutcome : outcome y = true) :
    ∀ {z}, graph.edge z u = true → treatment u = false → TreatmentAncestor graph treatment u →
      ∃ w, outcome w = true ∧ DirectedPath graph (Marginalized graph treatment outcome) z w := by
  induction path with
  | @single u y edge =>
    intro z entry uOutside reached
    cases uOutcome : outcome u with
    | true => exact ⟨u, uOutcome, .single entry⟩
    | false =>
      have causal : CausalNode graph treatment outcome u :=
        causal_node_iff.mpr ⟨uOutside, reached, y, endOutcome, .inr (.single edge)⟩
      exact ⟨y, endOutcome, .prepend entry ⟨causal_node_forbidden causal, uOutside, uOutcome⟩
        (.single edge)⟩
  | @prepend u v y edge vOutside tail ih =>
    intro z entry uOutside reached
    cases uOutcome : outcome u with
    | true => exact ⟨u, uOutcome, .single entry⟩
    | false =>
      have causal : CausalNode graph treatment outcome u :=
        causal_node_iff.mpr ⟨uOutside, reached, y, endOutcome, .inr (.prepend edge vOutside tail)⟩
      obtain ⟨w, wOutcome, projectedTail⟩ := ih endOutcome edge vOutside (walk_to_next edge reached)
      exact ⟨w, wOutcome, .prepend entry ⟨causal_node_forbidden causal, uOutside, uOutcome⟩
        projectedTail⟩

private theorem reached_outcome_is_causal {graph : DAG n} {treatment outcome : Fin n → Bool}
    (disjoint : ∀ y, outcome y = true → treatment y = false)
    (outcomesReached : ∀ y, outcome y = true → TreatmentAncestor graph treatment y)
    {y : Fin n} (inOutcome : outcome y = true) : CausalNode graph treatment outcome y :=
  causal_node_iff.mpr ⟨disjoint y inOutcome, outcomesReached y inOutcome, y, inOutcome, .inl rfl⟩

/-- Proposition 10 for finite DAGs, with arbitrary disjoint treatment and
outcome sets and every outcome descended from a treatment. -/
theorem o_set_iff_projected_parent (graph : DAG n) (treatment outcome : Fin n → Bool)
    (disjoint : ∀ y, outcome y = true → treatment y = false)
    (outcomesReached : ∀ y, outcome y = true → TreatmentAncestor graph treatment y)
    (v : Fin n) : OSet graph treatment outcome v ↔ ProjectedOSet graph treatment outcome v := by
  constructor
  · rintro ⟨⟨c, causal, entry⟩, vNotForbidden⟩
    have vOutside : treatment v = false := by
      cases h : treatment v with
      | false => rfl
      | true => exact False.elim (vNotForbidden (.inl h))
    have vNotOutcome : outcome v = false := by
      cases h : outcome v with
      | false => rfl
      | true => exact False.elim (vNotForbidden
          (causal_node_forbidden (reached_outcome_is_causal disjoint outcomesReached h)))
    obtain ⟨cOutside, reached, y, yOutcome, same | tail⟩ := causal_node_iff.mp causal
    · subst y
      exact ⟨vOutside, vNotOutcome, c, yOutcome, fun hidden => vNotForbidden hidden.1,
        fun hidden => by simp [Marginalized, yOutcome] at hidden, .single entry⟩
    · obtain ⟨w, wOutcome, path⟩ := projected_path_to_first_outcome tail yOutcome entry cOutside reached
      exact ⟨vOutside, vNotOutcome, w, wOutcome, fun hidden => vNotForbidden hidden.1,
        fun hidden => by simp [Marginalized, wOutcome] at hidden, path⟩
  · rintro ⟨vOutside, vNotOutcome, y, yOutcome, vKept, _, path⟩
    refine ⟨?_, fun h => vKept ⟨h, vOutside, vNotOutcome⟩⟩
    cases path with
    | single edge => exact ⟨y, reached_outcome_is_causal disjoint outcomesReached yOutcome, edge⟩
    | @prepend _ u _ entry hidden tail =>
      have reaches := treatment_ancestor_of_forbidden hidden.1 hidden.2.1
      have properTail := tail.relax (q := fun w => treatment w = false) (fun _ h => h.2.1)
      refine ⟨u, causal_node_iff.mpr ⟨hidden.2.1, reaches, ?_⟩, entry⟩
      exact ⟨y, yOutcome, .inr properTail⟩

end

end OpenCausalScience.Papers.WitteEtAl2020.ForbiddenProjection

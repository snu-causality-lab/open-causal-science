module
public import OpenCausalScience.Papers.Tian2004.ConditionalDecision
public import OpenCausalScience.Papers.Tian2004.QueryIntrinsic

/-! # The two conditional failure decisions

Tian's Phase 4 with the original component Identify failures agrees
with intrinsic-district failure in the joint query that remains after
IDC has exhausted its Rule 2 exchanges.
-/

namespace OpenCausalScience.Papers.Tian2004.ExactConditionalDecision

open TianPearl2003.IdentifyRecurrence
open ConditionalDecision FactorClosure IntrinsicIdentify QueryIntrinsic Reduction

@[expose] public section

variable {n : Nat}

/-- At a live vertex `d`, Phase 2's call on its district, starting from
the full graph's district containing `d`. -/
def ComponentSucceeds (G : MixedGraph n) (q : Query n) (d : Fin n) : Prop :=
  PlanSucceeds (identifyPlan G (verticesList (q.district G d)) d
    (district G (List.finRange n) d))

/-- Tian's Phase 4 guard tests the closed parent scopes of marked factors. -/
def PhaseFourFails (G : MixedGraph n) (q : Query n) : Prop :=
  ∃ v y, q.live G v ∧
    MarkedFactors G (q.live G) q.outcome q.evidence (fun d => ¬ ComponentSucceeds G q d) v ∧
    q.outcome y ∧ FactorGraph.scope G (q.live G) v y

theorem phase_four_fails_iff_idc_joint_fails {G : MixedGraph n} {start last : Query n}
    (rank : Fin n → Nat)
    (ranked : ∀ a b, G.edge a false b true = true → rank a < rank b)
    (directedMixed : ∀ u v, G.edge u false v false = false)
    (run : Exchanges G start last) (finished : Exhausted G last) :
    PhaseFourFails G start ↔ JointFails G last (Intrinsic G) := by
  apply Iff.trans ?_ (ConditionalDecision.phase_four_iff_idc_joint_fails
    directedMixed run finished (Intrinsic G))
  constructor
  · rintro ⟨v, y, here, ⟨d, fails, live, path⟩, outcome, scope⟩
    have same := query_component_identify_iff_intrinsic rank ranked live
    exact ⟨v, y, here, ⟨d, fun good => fails (same.mpr good), live, path⟩, outcome, scope⟩
  · rintro ⟨v, y, here, ⟨d, fails, live, path⟩, outcome, scope⟩
    have same := query_component_identify_iff_intrinsic rank ranked live
    exact ⟨v, y, here, ⟨d, fun good => fails (same.mp good), live, path⟩, outcome, scope⟩

end

end OpenCausalScience.Papers.Tian2004.ExactConditionalDecision

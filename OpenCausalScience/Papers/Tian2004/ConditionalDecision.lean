module
public import OpenCausalScience.Papers.Tian2004.FactorClosure
public import OpenCausalScience.Papers.Tian2004.RuleTwoQuery

/-! Connect the Phase 4 failure test from Tian (2004) to the exact joint
query used by IDC after all Rule 2 exchanges. Only the decision about
intrinsic districts is needed from joint ID. -/

namespace OpenCausalScience.Papers.Tian2004.ConditionalDecision

open FactorGraph FactorClosure Reduction RuleTwoIncidence RuleTwoQuery

@[expose] public section

variable {n : Nat}

/-- The graph test in IDC for exchanging one observed value for action. -/
def CanExchange (G : MixedGraph n) (q : Query n) (z : Fin n) : Prop :=
  ¬ (exchangeCut G q.allowed z).WalkConnected
    (singleton z) (membership q.outcome) (exchangeEvidence q.allowed q.evidence z)

inductive Exchanges (G : MixedGraph n) (start : Query n) : Query n → Prop
  | refl : Exchanges G start start
  | step {q} : Exchanges G start q → (z : Fin n) → (hz : q.evidence z) →
      CanExchange G q z → Exchanges G start (q.move z hz)

def Exhausted (G : MixedGraph n) (q : Query n) : Prop :=
  ∀ z, q.evidence z → ¬ CanExchange G q z

theorem exchanges_iff_moves {G : MixedGraph n} {start last : Query n}
    (directedMixed : ∀ u v, G.edge u false v false = false) :
    Exchanges G start last ↔ Moves G start last := by
  constructor
  · intro trace
    induction trace with
    | refl => exact .refl
    | step _ z hz usable ih =>
      exact .step ih z hz ((rule_two_separated_iff_not_linked hz directedMixed).mp usable)
  · intro trace
    induction trace with
    | refl => exact .refl
    | step _ z hz usable ih =>
      exact .step ih z hz ((rule_two_separated_iff_not_linked hz directedMixed).mpr usable)

theorem exhausted_iff_stationary {G : MixedGraph n} {q : Query n}
    (directedMixed : ∀ u v, G.edge u false v false = false) :
    Exhausted G q ↔ Stationary G q := by
  constructor
  · intro exhausted z hz
    apply Classical.byContradiction
    exact fun unlinked => exhausted z hz ((rule_two_separated_iff_not_linked hz directedMixed).mpr unlinked)
  · intro stationary z hz usable
    exact ((rule_two_separated_iff_not_linked hz directedMixed).mp usable) (stationary z hz)

theorem exists_exhausted_exchange_run (G : MixedGraph n) (start : Query n)
    (directedMixed : ∀ u v, G.edge u false v false = false) :
    ∃ last, Exchanges G start last ∧ Exhausted G last := by
  obtain ⟨last, run, done⟩ := exists_stationary_run G start
  exact ⟨last, (exchanges_iff_moves directedMixed).mpr run, (exhausted_iff_stationary directedMixed).mpr done⟩

/-- The observations remaining after all exchanges are precisely the
original observations whose factors are linked to the outcome. -/
theorem retained_evidence_iff_linked {G : MixedGraph n} {start last : Query n}
    (directedMixed : ∀ u v, G.edge u false v false = false)
    (run : Exchanges G start last) (finished : Exhausted G last) (z : Fin n) :
    last.evidence z ↔ start.evidence z ∧ start.linked G z :=
  ((exchanges_iff_moves directedMixed).mp run).stationary_evidence_iff
    ((exhausted_iff_stationary directedMixed).mp finished) z

/-- After any maximal sequence of actual Rule 2 exchanges, Tian's
failure predicate agrees with the joint ID failure predicate. -/
theorem tian_fails_iff_idc_joint_fails {G : MixedGraph n} {start last : Query n}
    (directedMixed : ∀ u v, G.edge u false v false = false)
    (run : Exchanges G start last) (finished : Exhausted G last)
    (intrinsic : Vertices n → Prop) :
    TianFails G start intrinsic ↔ JointFails G last intrinsic :=
  tian_fails_iff_joint_fails ((exchanges_iff_moves directedMixed).mp run)
    ((exhausted_iff_stationary directedMixed).mp finished) intrinsic

/-- The original Phase 4 scope intersection equals the failure
predicate on the exact reduced joint. -/
theorem phase_four_iff_idc_joint_fails {G : MixedGraph n} {start last : Query n}
    (directedMixed : ∀ u v, G.edge u false v false = false)
    (run : Exchanges G start last) (finished : Exhausted G last)
    (intrinsic : Vertices n → Prop) :
    (∃ v y, start.live G v ∧
      MarkedFactors G (start.live G) start.outcome start.evidence
        (fun d => ¬ intrinsic (start.district G d)) v ∧
      start.outcome y ∧ scope G (start.live G) v y) ↔
    JointFails G last intrinsic :=
  (phase_four_iff_tian_fails G start intrinsic).trans
    (tian_fails_iff_idc_joint_fails directedMixed run finished intrinsic)

end
end OpenCausalScience.Papers.Tian2004.ConditionalDecision

module
public import Std

/-! The comparison variable in Mohan and Pearl (2014), Theorem 1. Response
indicators needed to observe any queried variable are held at the observed
value. This does not change whether an eligible comparison variable exists. -/

@[expose] public section

namespace OpenCausalScience.Papers.MohanPearl2014.ComparisonWitnesses

def IndicatorOf {V : Type} (response : V → Option V)
    (members : V → Prop) (indicator : V) : Prop :=
  ∃ v, members v ∧ response v = some indicator

theorem exists_comparison_with_responses_fixed {V : Type} (response : V → Option V)
    (X Y Z : V → Prop)
    (rolesDisjoint : ∀ {v r}, response v = some r → response r = none) :
    (∃ y, Y y ∧ ¬ IndicatorOf response X y ∧ ¬ IndicatorOf response Z y) ↔
      ∃ y, Y y ∧ ¬ IndicatorOf response X y ∧ ¬ IndicatorOf response Y y ∧
        ¬ IndicatorOf response Z y := by
  classical
  constructor
  · rintro ⟨y, member, noX, noZ⟩
    by_cases h : IndicatorOf response Y y
    · obtain ⟨v, inY, indicator⟩ := h
      have notIndicator (members : V → Prop) : ¬ IndicatorOf response members v := by
        rintro ⟨u, _, assigned⟩
        have contradiction := rolesDisjoint assigned
        rw [indicator] at contradiction
        contradiction
      exact ⟨v, inY, notIndicator X, notIndicator Y, notIndicator Z⟩
    · exact ⟨y, member, noX, h, noZ⟩
  · rintro ⟨y, member, noX, _, noZ⟩
    exact ⟨y, member, noX, noZ⟩

end OpenCausalScience.Papers.MohanPearl2014.ComparisonWitnesses

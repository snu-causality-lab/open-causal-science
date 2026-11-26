module
public import OpenCausalScience.Papers.CorreaTianBareinboim2018.Figure2
public import OpenCausalScience.Papers.CorreaTianBareinboim2018.Recovery

/-! # Figure 2's adjustment derivation

Correa, Tian and Bareinboim (2018), equation (5) and Appendix
equations (8)–(16). The proof follows the appendix's two total
probability expansions, treatment and selection exchanges, and
normalization. The exchanges are supplied as kernel identities.
Source: https://causalai.net/r29.pdf#page=9
-/

namespace OpenCausalScience.Papers.CorreaTianBareinboim2018.Figure2Recovery

open Recovery

@[expose] public section

variable {X Y Z₁ Z₂ Z₃ : Type}

def selectedSecondThird (data : Sources X Y Z₂ (Z₁ × Z₃)) (first : List Z₁)
    (b : Z₂) (c : Z₃) : Rat :=
  sumOver first fun a => data.selectedCovariates b (a, c)

def selectedThird (data : Sources X Y Z₂ (Z₁ × Z₃)) (first : List Z₁)
    (b : Z₂) (c : Z₃) : Rat :=
  selectedSecondThird data first b c / data.selectedExternal b

def selectedFirst (data : Sources X Y Z₂ (Z₁ × Z₃)) (first : List Z₁)
    (a : Z₁) (b : Z₂) (c : Z₃) : Rat :=
  data.selectedCovariates b (a, c) / selectedSecondThird data first b c

/-- The kernel identities used by the appendix. The fixed x,y are the
treatment and outcome assignments of equation (5). -/
structure Derivation (data : Sources X Y Z₂ (Z₁ × Z₃)) (x : X) (y : Y)
    (first : List Z₁) (third : List Z₃) where
  effect : Rat
  populationThird : Z₃ → Rat
  populationSecondThird : Z₂ → Z₃ → Rat
  treatedGivenThird : Z₃ → Rat
  treatedGivenSecondThird : Z₂ → Z₃ → Rat
  treatedSecondGivenThird : Z₂ → Z₃ → Rat
  selectedTreatedGivenSecondThird : Z₂ → Z₃ → Rat
  selectedTreatedGivenAll : Z₁ → Z₂ → Z₃ → Rat
  selectedTreatedFirst : Z₁ → Z₂ → Z₃ → Rat
  third_normalized : sumOver third populationThird = 1
  third_supported : ∀ c ∈ third, populationThird c ≠ 0
  selected_second_third_supported :
    ∀ b ∈ data.external, ∀ c ∈ third, selectedSecondThird data first b c ≠ 0
  outcome_ignores_third : ∀ c ∈ third, treatedGivenThird c = effect
  condition_on_second : ∀ c ∈ third, treatedGivenThird c =
    sumOver data.external fun b => treatedGivenSecondThird b c * treatedSecondGivenThird b c
  second_exchange : ∀ b ∈ data.external, ∀ c ∈ third,
    treatedSecondGivenThird b c = populationSecondThird b c / populationThird c
  outcome_selection : ∀ b ∈ data.external, ∀ c ∈ third,
    treatedGivenSecondThird b c = selectedTreatedGivenSecondThird b c
  condition_on_first : ∀ b ∈ data.external, ∀ c ∈ third, selectedTreatedGivenSecondThird b c =
    sumOver first fun a => selectedTreatedGivenAll a b c * selectedTreatedFirst a b c
  outcome_exchange : ∀ a ∈ first, ∀ b ∈ data.external, ∀ c ∈ third,
    selectedTreatedGivenAll a b c = data.selectedResponse x y b (a, c)
  first_exchange : ∀ a ∈ first, ∀ b ∈ data.external, ∀ c ∈ third,
    selectedTreatedFirst a b c = selectedFirst data first a b c
  third_selection : ∀ b ∈ data.external, ∀ c ∈ third,
    populationSecondThird b c = selectedThird data first b c * data.populationMargin b

private theorem chain_selected (data : Sources X Y Z₂ (Z₁ × Z₃)) (first : List Z₁)
    (a : Z₁) (b : Z₂) (c : Z₃) (nonzero : selectedSecondThird data first b c ≠ 0) :
    selectedFirst data first a b c * selectedThird data first b c = data.selectedRemainder b (a, c) := by
  unfold selectedFirst selectedThird Sources.selectedRemainder
  rw [Rat.div_def (selectedSecondThird data first b c) (data.selectedExternal b),
    ← Rat.mul_assoc, Rat.div_mul_cancel nonzero, Rat.div_def]

theorem figure2_adjustment_formula (data : Sources X Y Z₂ (Z₁ × Z₃)) (x : X) (y : Y)
    (first : List Z₁) (third : List Z₃)
    (rest : data.remainder = third.flatMap (fun c => first.map (·, c)))
    (laws : Derivation data x y first third) :
    laws.effect = data.recover x y := by
  calc
    _ = sumOver third (fun c => laws.treatedGivenThird c * laws.populationThird c) := by
      symm
      calc
        _ = sumOver third (fun c => laws.effect * laws.populationThird c) :=
          sum_congr _ _ _ (fun c present => by rw [laws.outcome_ignores_third c present])
        _ = sumOver third (fun c => laws.populationThird c * laws.effect) :=
          sum_congr _ _ _ (fun c _ => Rat.mul_comm _ _)
        _ = _ := by rw [sum_mul_right, laws.third_normalized, Rat.one_mul]
    _ = sumOver third (fun c => sumOver data.external
          (fun b => laws.selectedTreatedGivenSecondThird b c * laws.populationSecondThird b c)) := by
      apply sum_congr
      intro c present
      rw [laws.condition_on_second c present, ← sum_mul_right]
      apply sum_congr
      intro b available
      rw [laws.second_exchange b available c present, laws.outcome_selection b available c present,
        Rat.mul_assoc, Rat.div_mul_cancel (laws.third_supported c present)]
    _ = sumOver data.external (fun b => sumOver third
          (fun c => laws.selectedTreatedGivenSecondThird b c * laws.populationSecondThird b c)) :=
      sum_swap _ _ _
    _ = data.recover x y := by
      unfold Sources.recover adjustment
      apply sum_congr
      intro b available
      rw [rest, sum_flat_map]
      apply sum_congr
      intro c present
      rw [laws.condition_on_first b available c present, laws.third_selection b available c present,
        ← sum_mul_right, sum_map]
      apply sum_congr
      intro a member
      rw [laws.outcome_exchange a member b available c present,
        laws.first_exchange a member b available c present,
        ← Rat.mul_assoc _ (selectedThird data first b c) (data.populationMargin b),
        Rat.mul_assoc (data.selectedResponse x y b (a, c))
          (selectedFirst data first a b c) (selectedThird data first b c),
        chain_selected data first a b c (laws.selected_second_third_supported b available c present)]

theorem figure2_recovery_from_supported_sources
    (data : Sources X Y Z₂ (Z₁ × Z₃)) (x : X) (y : Y)
    (first : List Z₁) (third : List Z₃)
    (rest : data.remainder = third.flatMap (fun c => first.map (·, c)))
    (laws : Derivation data x y first third) (support : data.supports x = true) :
    data.recoverSupported x y = some laws.effect := by
  rw [data.recover_supported x y ((data.supports_iff x).mp support),
    ← figure2_adjustment_formula data x y first third rest laws]

end

end OpenCausalScience.Papers.CorreaTianBareinboim2018.Figure2Recovery

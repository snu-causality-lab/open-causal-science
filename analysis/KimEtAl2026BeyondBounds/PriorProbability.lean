import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map

/-!
# Prior probability of an interval effect and of tolerance fairness

Kim, Cho, and Lee (UAI 2026), Lemma 4 and Appendix B.3.
https://proceedings.mlr.press/v337/kim26b.html

Given the measurable reduced effects and projection, the contribution of Lemma 4 is measured
exactly under any chosen reduced prior. For a full-space prior, equality with the full-space
event uses its pushforward under the projection. Nonnegative integrals of the constant one
represent the paper's event probabilities. The tolerance condition quantifies over the finite
set of supported queries, as in Definition 5.
-/

namespace KimEtAl2026BeyondBounds

open MeasureTheory

variable {Θ Φ : Type*} [MeasurableSpace Θ] [MeasurableSpace Φ]

def effectInterval {Space : Type*} (g : Space → ℝ) (l r : ℝ) : Set Space :=
  {φ | l ≤ g φ ∧ g φ ≤ r}

theorem measurable_set_effect_interval (g : Φ → ℝ) (hg : Measurable g) (l r : ℝ) :
    MeasurableSet (effectInterval g l r) :=
  (measurableSet_le measurable_const hg).inter (measurableSet_le hg measurable_const)

def toleranceFairness {Space I : Type*} (g : I → Space → ℝ) (τ : ℝ) : Set Space :=
  {φ | ∀ i, |g i φ| ≤ τ}

omit [MeasurableSpace Φ] in
theorem tolerance_fairness_eq_inter {I : Type*} (g : I → Φ → ℝ) (τ : ℝ) :
    toleranceFairness g τ = ⋂ i, effectInterval (g i) (-τ) τ := by
  ext φ
  simp [toleranceFairness, effectInterval, abs_le]

theorem measurable_set_tolerance_fairness {I : Type*} [Fintype I]
    (g : I → Φ → ℝ) (hg : ∀ i, Measurable (g i)) (τ : ℝ) :
    MeasurableSet (toleranceFairness g τ) := by
  rw [tolerance_fairness_eq_inter]
  exact MeasurableSet.iInter fun i => measurable_set_effect_interval (g i) (hg i) (-τ) τ

private theorem measure_eq_integral_one (μ : Measure Φ) (A : Set Φ) :
    μ A = ∫⁻ _ in A, 1 ∂μ := by
  simp [lintegral_const, Measure.restrict_apply MeasurableSet.univ]

theorem interval_probability (μ : Measure Φ) (g : Φ → ℝ) (l r : ℝ) :
    μ (effectInterval g l r) = ∫⁻ _ in effectInterval g l r, 1 ∂μ :=
  measure_eq_integral_one μ _

theorem tolerance_fairness_probability {I : Type*} (μ : Measure Φ) (g : I → Φ → ℝ) (τ : ℝ) :
    μ (toleranceFairness g τ) = ∫⁻ _ in toleranceFairness g τ, 1 ∂μ :=
  measure_eq_integral_one μ _

theorem interval_probability_pushforward (μ : Measure Θ) (π : Θ → Φ) (hπ : Measurable π)
    (g : Φ → ℝ) (hg : Measurable g) (effect : Θ → ℝ)
    (dependsOnReduced : ∀ θ, effect θ = g (π θ)) (l r : ℝ) :
    μ (effectInterval effect l r) =
      ∫⁻ _ in effectInterval g l r, 1 ∂(Measure.map π μ) := by
  rw [← interval_probability, Measure.map_apply hπ (measurable_set_effect_interval g hg l r)]
  congr 1
  ext θ
  simp [effectInterval, dependsOnReduced]

theorem tolerance_fairness_probability_pushforward {I : Type*} [Fintype I]
    (μ : Measure Θ) (π : Θ → Φ) (hπ : Measurable π)
    (g : I → Φ → ℝ) (hg : ∀ i, Measurable (g i)) (effect : I → Θ → ℝ)
    (dependsOnReduced : ∀ i θ, effect i θ = g i (π θ)) (τ : ℝ) :
    μ (toleranceFairness effect τ) =
      ∫⁻ _ in toleranceFairness g τ, 1 ∂(Measure.map π μ) := by
  rw [← tolerance_fairness_probability,
    Measure.map_apply hπ (measurable_set_tolerance_fairness g hg τ)]
  congr 1
  ext θ
  simp [toleranceFairness, dependsOnReduced]

end KimEtAl2026BeyondBounds

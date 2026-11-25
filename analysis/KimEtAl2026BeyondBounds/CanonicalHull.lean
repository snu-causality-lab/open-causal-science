import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Ring

/-!
# Canonical hull in C-parameters

Kim, Cho, and Lee (UAI 2026), Lemma 2 and Appendix B.1.
https://proceedings.mlr.press/v337/kim26b.html

Each exogenous block uses the finite canonical response-function domain of one C-component.
The Boolean row records the product of the deterministic response indicators for one Q-factor
entry. The observational Q-factor identification and product factorization premises state the
interface to Lemma 1. From these premises we prove exact membership in the hull by a finite
bounded linear system and convexity over the reals.
-/

namespace KimEtAl2026BeyondBounds

noncomputable section

open scoped BigOperators

variable {Component : Type*}
variable {Response : Component → Type*} [∀ i, Fintype (Response i)]
variable {Row : Component → Type*}
variable {Assignment : Type*}

abbrev Parameters (Response : Component → Type*) := (i : Component) → Response i → ℝ

/-- Equation (9), which gives a probability distribution for each C-component. -/
def NormalizedBlocks (θ : Parameters Response) : Prop :=
  (∀ i u, 0 ≤ θ i u ∧ θ i u ≤ 1) ∧ ∀ i, ∑ u, θ i u = 1

/-- The real-valued entries in the response indicator matrix. -/
def indicatorCoefficient
    (indicator : (i : Component) → Row i → Response i → Bool)
    (i : Component) (r : Row i) (u : Response i) : ℝ :=
  if indicator i r u then 1 else 0

/-- Each row is supported on one C-component's response weights. -/
def blockLinear (coefficient : (i : Component) → Row i → Response i → ℝ)
    (θ : Parameters Response) (i : Component) (r : Row i) : ℝ :=
  ∑ u, coefficient i r u * θ i u

/-- One entry of the Q-factor in Equation (10). -/
def qFactor (indicator : (i : Component) → Row i → Response i → Bool)
    (θ : Parameters Response) (i : Component) (r : Row i) : ℝ :=
  blockLinear (indicatorCoefficient indicator) θ i r

/-- The observed distribution under the factorization in Lemma 1. -/
def observationalMass [Fintype Component]
    (indicator : (i : Component) → Row i → Response i → Bool)
    (observedRow : (i : Component) → Assignment → Row i)
    (θ : Parameters Response) (v : Assignment) : ℝ :=
  ∏ i, qFactor indicator θ i (observedRow i v)

/-- Definition 7 for canonical C-parameters with the supplied observational factorization. -/
def canonicalHull [Fintype Component]
    (indicator : (i : Component) → Row i → Response i → Bool)
    (observedRow : (i : Component) → Assignment → Row i)
    (pObserved : Assignment → ℝ) : Set (Parameters Response) :=
  {θ | NormalizedBlocks θ ∧ ∀ v, observationalMass indicator observedRow θ v = pObserved v}

/-- The finite constraints (9) and (10), expressed in block coordinates. -/
def linearConstraintSet
    (coefficient : (i : Component) → Row i → Response i → ℝ)
    (target : (i : Component) → Row i → ℝ) : Set (Parameters Response) :=
  {θ | NormalizedBlocks θ ∧ ∀ i r, blockLinear coefficient θ i r = target i r}

variable (indicator : (i : Component) → Row i → Response i → Bool)
variable (observedRow : (i : Component) → Assignment → Row i)
variable (pObserved : Assignment → ℝ)
variable (observedQ : (i : Component) → Row i → ℝ)

theorem canonical_hull_eq_linear_constraints [Fintype Component]
    (qFromObservation : ∀ θ, NormalizedBlocks θ →
      (∀ v, observationalMass indicator observedRow θ v = pObserved v) →
      ∀ i r, qFactor indicator θ i r = observedQ i r)
    (observedFactorization : ∀ v, (∏ i, observedQ i (observedRow i v)) = pObserved v) :
    canonicalHull indicator observedRow pObserved = linearConstraintSet (indicatorCoefficient indicator) observedQ := by
  ext θ
  constructor
  · rintro ⟨normal, agrees⟩
    exact ⟨normal, qFromObservation θ normal agrees⟩
  · rintro ⟨normal, agrees⟩
    refine ⟨normal, fun v => ?_⟩
    unfold observationalMass
    rw [← observedFactorization v]
    exact Finset.prod_congr rfl fun i _ => agrees i (observedRow i v)

variable (coefficient : (i : Component) → Row i → Response i → ℝ)
variable (target : (i : Component) → Row i → ℝ)

private theorem block_linear_affine (θ ψ : Parameters Response) (a b : ℝ)
    (i : Component) (r : Row i) :
    blockLinear coefficient (a • θ + b • ψ) i r =
      a * blockLinear coefficient θ i r + b * blockLinear coefficient ψ i r := by
  simp only [blockLinear, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem linear_constraints_convex : Convex ℝ (linearConstraintSet coefficient target) := by
  intro θ hθ ψ hψ a b ha hb hab
  rcases hθ with ⟨⟨θbox, θmass⟩, θq⟩
  rcases hψ with ⟨⟨ψbox, ψmass⟩, ψq⟩
  refine ⟨⟨fun i u => ?_, fun i => ?_⟩, fun i r => ?_⟩
  · obtain ⟨θnonneg, θle⟩ := θbox i u
    obtain ⟨ψnonneg, ψle⟩ := ψbox i u
    change 0 ≤ a * θ i u + b * ψ i u ∧ a * θ i u + b * ψ i u ≤ 1
    constructor
    · exact add_nonneg (mul_nonneg ha θnonneg) (mul_nonneg hb ψnonneg)
    · calc
        a * θ i u + b * ψ i u ≤ a * 1 + b * 1 := by
          exact add_le_add (mul_le_mul_of_nonneg_left θle ha)
            (mul_le_mul_of_nonneg_left ψle hb)
        _ = 1 := by simpa using hab
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    rw [θmass, ψmass]
    simpa using hab
  · rw [block_linear_affine, θq, ψq, ← add_mul, hab, one_mul]

theorem linear_constraints_subset_unit_box :
    linearConstraintSet coefficient target ⊆ Set.Icc (0 : Parameters Response) 1 := by
  intro θ hθ
  exact ⟨fun i u => (hθ.1.1 i u).1, fun i u => (hθ.1.1 i u).2⟩

theorem canonical_hull_convex_and_bounded [Fintype Component]
    (qFromObservation : ∀ θ, NormalizedBlocks θ →
      (∀ v, observationalMass indicator observedRow θ v = pObserved v) →
      ∀ i r, qFactor indicator θ i r = observedQ i r)
    (observedFactorization : ∀ v, (∏ i, observedQ i (observedRow i v)) = pObserved v) :
    Convex ℝ (canonicalHull indicator observedRow pObserved) ∧
      canonicalHull indicator observedRow pObserved ⊆ Set.Icc (0 : Parameters Response) 1 := by
  rw [canonical_hull_eq_linear_constraints indicator observedRow pObserved observedQ
    qFromObservation observedFactorization]
  exact ⟨linear_constraints_convex (indicatorCoefficient indicator) observedQ,
    linear_constraints_subset_unit_box (indicatorCoefficient indicator) observedQ⟩

end

end KimEtAl2026BeyondBounds

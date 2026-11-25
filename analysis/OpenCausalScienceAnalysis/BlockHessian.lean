module
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Fin.Basic

/-! # The full block-Hessian unknowns in Equations (10) and (11)

The [corrected version](https://www.sanghacklee.me/ai-corrected/CRL_internal_auxiliaries_AI_corrected_2026-10-15.pdf)
uses a homogeneous linear system for each pair of learned coordinates from
distinct learned blocks. This file indexes the unknowns by the three types of
terms printed in Equations (10) and (11) and proves the block-gradient
exclusion from injectivity of the coefficient map. The density identity,
chain rule, coefficient construction, and pointwise block matching are
separate steps in the argument.
-/

namespace OpenCausalScience.Papers.KimEtAl2026.BlockHessian

@[expose] public section

variable {n : ℕ} {κ R : Type*}

/-- Unknowns in the homogeneous system for a pair of learned coordinates.
Each within-block off-diagonal coordinate pair occurs once in increasing order. -/
inductive DerivativeTerm (block : Fin n → κ) where
  | mixed (a : Fin n)
  | diagonal (a : Fin n)
  | offDiagonal (a b : Fin n) (ordered : a < b) (sameBlock : block a = block b)

/-- The two first-derivative vectors and their mixed derivative, indexed as
specified in Equations (10) and (11). -/
def derivativeTerms {block : Fin n → κ} (mixed a b : Fin n → ℝ) : DerivativeTerm block → ℝ
  | .mixed i => mixed i
  | .diagonal i => a i * b i
  | .offDiagonal i j _ _ => a i * b j + a j * b i

/-- For a fixed pair of learned coordinates, the full-rank homogeneous system
forces every indexed derivative term to be zero. -/
theorem derivative_terms_eq_zero_of_injective_system {block : Fin n → κ}
    (coefficients : (DerivativeTerm block → ℝ) →ₗ[ℝ] (R → ℝ))
    (fullRank : Function.Injective coefficients) {mixed a b : Fin n → ℝ}
    (equations : coefficients (derivativeTerms mixed a b) = 0) :
    derivativeTerms (block := block) mixed a b = 0 :=
  fullRank (by simpa only [map_zero] using equations)

/-- Two learned coordinates from different blocks cannot both have nonzero
block gradients in the same true block under the injective system.
The statement applies to each pair to which Equations (10) or (11) apply. -/
theorem block_gradients_excluded_of_injective_system {block : Fin n → κ}
    (coefficients : (DerivativeTerm block → ℝ) →ₗ[ℝ] (R → ℝ))
    (fullRank : Function.Injective coefficients) {mixed a b : Fin n → ℝ}
    (equations : coefficients (derivativeTerms mixed a b) = 0) (k : κ) :
    (∀ i, block i = k → a i = 0) ∨ (∀ i, block i = k → b i = 0) := by
  classical
  have terms := derivative_terms_eq_zero_of_injective_system coefficients fullRank equations
  by_cases all : ∀ i, block i = k → a i = 0
  · exact Or.inl all
  obtain ⟨i, hiBlock, hi⟩ : ∃ i, block i = k ∧ a i ≠ 0 := by
    by_contra h
    apply all
    intro i hiBlock
    by_contra hi
    exact h ⟨i, hiBlock, hi⟩
  have diagonal : a i * b i = 0 := congrFun terms (.diagonal i)
  have bi : b i = 0 := (mul_eq_zero.mp diagonal).resolve_left hi
  right
  intro j hjBlock
  by_cases same : i = j
  · subst j
    exact bi
  have sameBlock := hiBlock.trans hjBlock.symm
  have offDiagonal : a i * b j + a j * b i = 0 := by
    rcases lt_or_gt_of_ne same with ordered | ordered
    · exact congrFun terms (.offDiagonal i j ordered sameBlock)
    · exact (add_comm _ _).trans (congrFun terms (.offDiagonal j i ordered sameBlock.symm))
  rw [bi, mul_zero, add_zero] at offDiagonal
  exact (mul_eq_zero.mp offDiagonal).resolve_left hi

end
end OpenCausalScience.Papers.KimEtAl2026.BlockHessian

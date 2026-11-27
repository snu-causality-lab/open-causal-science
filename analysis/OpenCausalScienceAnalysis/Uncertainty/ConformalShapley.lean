import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

/-!
# Two-game attribution of conformal uncertainty

The finite real-valued Shapley formula in Eq. (1), its two-game decomposition
in Theorem 1, and the transformed-scale and fixed-group forms in Propositions
1 and 2. The CQR endpoint and LACP log-width identities connect the supplied
width summaries to the coalition games.

Source: Cho et al., NeurIPS 2026, public OpenReview submission `lZavBaxJ68`.
https://openreview.net/forum?id=lZavBaxJ68
-/

open scoped BigOperators

namespace OpenCausalScienceAnalysis.Uncertainty.ConformalShapley

noncomputable section

variable {d rows : ℕ}

abbrev Coalition (d : ℕ) := Finset (Fin d)

/-- The exact factorial-weight Shapley allocation over coalitions without `j`. -/
def shapley (game : Coalition d → ℝ) (j : Fin d) : ℝ :=
  ∑ S ∈ (Finset.univ.erase j).powerset,
    ((S.card.factorial : ℝ) * ((d - S.card - 1).factorial : ℝ) / (d.factorial : ℝ)) *
      (game (insert j S) - game S)

theorem shapley_linear (first second : Coalition d → ℝ) (a b : ℝ) (j : Fin d) :
    shapley (fun S => a * first S + b * second S) j =
      a * shapley first j + b * shapley second j := by
  simp only [shapley, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- Theorem 1. Assemble both games at the same coalition and allocate their total. -/
theorem two_game_decomposition (total instanceGame calibrationGame : Coalition d → ℝ)
    (additive : ∀ S, total S = instanceGame S + calibrationGame S) (j : Fin d) :
    shapley total j = shapley instanceGame j + shapley calibrationGame j := by
  have sameGame : total = (fun S => instanceGame S + calibrationGame S) := funext additive
  rw [sameGame]
  simpa only [one_mul] using shapley_linear instanceGame calibrationGame 1 1 j

/-- Keep the coalition's coordinates and replace the others by their common baseline. -/
def mask (baseline point : Fin d → ℝ) (S : Coalition d) : Fin d → ℝ :=
  fun j => if j ∈ S then point j else baseline j

/-- Proposition 1. Under separability, test-feature and calibration-column masking
give separate games whose Shapley allocations add on the transformed scale. -/
theorem transformed_width_decomposition
    (transform : ℝ → ℝ)
    (width : (Fin d → ℝ) → (Fin rows → Fin d → ℝ) → ℝ)
    (instanceWidth : (Fin d → ℝ) → ℝ)
    (calibrationWidth : (Fin rows → Fin d → ℝ) → ℝ)
    (separable : ∀ point calibration,
      transform (width point calibration) = instanceWidth point + calibrationWidth calibration)
    (baseline point : Fin d → ℝ) (calibration : Fin rows → Fin d → ℝ) (j : Fin d) :
    shapley (fun S => transform (width (mask baseline point S)
      (fun i => mask baseline (calibration i) S))) j =
      shapley (fun S => instanceWidth (mask baseline point S)) j +
      shapley (fun S => calibrationWidth (fun i => mask baseline (calibration i) S)) j :=
  two_game_decomposition _ _ _ (fun _ => separable _ _) j

/-- Proposition 2. In a fixed Mondrian group, using its calibration summary gives
the conditional decomposition. The group index stays fixed under feature masking. -/
theorem group_width_decomposition {Group : Type} (group : Group) (transform : ℝ → ℝ)
    (width : Group → (Fin d → ℝ) → (Fin rows → Fin d → ℝ) → ℝ)
    (instanceWidth : (Fin d → ℝ) → ℝ)
    (calibrationWidth : Group → (Fin rows → Fin d → ℝ) → ℝ)
    (separable : ∀ group point calibration,
      transform (width group point calibration) =
        instanceWidth point + calibrationWidth group calibration)
    (baseline point : Fin d → ℝ) (calibration : Fin rows → Fin d → ℝ) (j : Fin d) :
    shapley (fun S => transform (width group (mask baseline point S)
      (fun i => mask baseline (calibration i) S))) j =
      shapley (fun S => instanceWidth (mask baseline point S)) j +
      shapley (fun S => calibrationWidth group (fun i => mask baseline (calibration i) S)) j :=
  transformed_width_decomposition transform (width group) instanceWidth (calibrationWidth group)
    (separable group) baseline point calibration j

/-- CQR. The difference of corrected endpoints decomposes into the fitted width
and twice the conformal quantile of the masked calibration scores. -/
theorem cqr_attribution (lower upper quantile : Coalition d → ℝ) (j : Fin d) :
    shapley (fun S => (upper S + quantile S) - (lower S - quantile S)) j =
      shapley (fun S => upper S - lower S) j + shapley (fun S => 2 * quantile S) j := by
  apply two_game_decomposition
  intro S
  ring

/-- Section 5.2. A positive LACP scale and positive calibration quantile in
each coalition yield the two-game decomposition of log-width. -/
theorem lacp_log_attribution (scale quantile : Coalition d → ℝ)
    (positiveScale : ∀ S, 0 < scale S) (positiveQuantile : ∀ S, 0 < quantile S) (j : Fin d) :
    shapley (fun S => Real.log (scale S * (2 * quantile S))) j =
      shapley (fun S => Real.log (scale S)) j + shapley (fun S => Real.log (2 * quantile S)) j := by
  apply two_game_decomposition
  intro S
  exact Real.log_mul (ne_of_gt (positiveScale S))
    (mul_ne_zero two_ne_zero (ne_of_gt (positiveQuantile S)))

end

end OpenCausalScienceAnalysis.Uncertainty.ConformalShapley

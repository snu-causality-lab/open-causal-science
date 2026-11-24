module
public import Std

/-!
# Lee and Honavar (2017), deletion and empirical upper tails

Appendix C of the September 2026 correction keeps track of the changed
denominator after removing off-diagonal terms. The statements below prove
its deterministic scalar bound over rational inputs. They begin with the
bounds on the omitted sum and on the retained mean. Section 4.4's constant
data issue is expressed separately as a change to the empirical upper tail.
-/

namespace OpenCausalScience.Papers.LeeHonavar2017.DeletionBound

@[expose] public section

/-- The difference between the original mean and the retained mean includes
both the omitted sum and the changed denominator. -/
theorem renormalized_difference (allCount deletedCount retainedMean deletedSum : Rat)
    (positiveCount : 0 < allCount) :
    ((allCount - deletedCount) * retainedMean + deletedSum) / allCount - retainedMean =
      (deletedSum - deletedCount * retainedMean) / allCount := by
  have nonzero := Rat.ne_of_gt positiveCount
  have scaled :
      (((allCount - deletedCount) * retainedMean + deletedSum) / allCount - retainedMean) *
        allCount = ((deletedSum - deletedCount * retainedMean) / allCount) * allCount := by
    simp only [Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul, Rat.div_mul_cancel nonzero]
    grind
  simpa only [Rat.mul_div_cancel nonzero] using congrArg (· / allCount) scaled

/-- If terms are bounded in absolute value by B, renormalization gives the
factor 2 in the bound on the difference of the means. -/
theorem renormalized_deletion_bound (allCount deletedCount retainedMean deletedSum bound : Rat)
    (positiveCount : 0 < allCount) (nonnegDeleted : 0 ≤ deletedCount)
    (retainedLower : -bound ≤ retainedMean) (retainedUpper : retainedMean ≤ bound)
    (deletedLower : -(bound * deletedCount) ≤ deletedSum)
    (deletedUpper : deletedSum ≤ bound * deletedCount) :
    (((allCount - deletedCount) * retainedMean + deletedSum) / allCount - retainedMean).abs ≤
      (2 * bound * deletedCount) / allCount := by
  rw [renormalized_difference _ _ _ _ positiveCount]
  have nonzero := Rat.ne_of_gt positiveCount
  have mulLower := Rat.mul_le_mul_of_nonneg_left retainedLower nonnegDeleted
  have mulUpper := Rat.mul_le_mul_of_nonneg_left retainedUpper nonnegDeleted
  unfold Rat.abs
  split
  · apply Rat.le_of_mul_le_mul_right _ positiveCount
    rw [Rat.div_mul_cancel nonzero, Rat.div_mul_cancel nonzero]
    grind
  · apply Rat.le_of_mul_le_mul_right _ positiveCount
    rw [Rat.neg_mul, Rat.div_mul_cancel nonzero, Rat.div_mul_cancel nonzero]
    grind

/-- Appendix C's final finite-sample deletion bound, with B = 4C² and at
most 2n deleted directed pairs from n(n−1) off-diagonal pairs. -/
theorem mmsd_deletion_bound (n c deletedCount retainedMean deletedSum : Rat)
    (nLarge : 1 < n) (countLower : 0 ≤ deletedCount) (countUpper : deletedCount ≤ 2 * n)
    (retainedLower : -(4 * c * c) ≤ retainedMean) (retainedUpper : retainedMean ≤ 4 * c * c)
    (deletedLower : -((4 * c * c) * deletedCount) ≤ deletedSum)
    (deletedUpper : deletedSum ≤ (4 * c * c) * deletedCount) :
    (((n * (n - 1) - deletedCount) * retainedMean + deletedSum) /
      (n * (n - 1)) - retainedMean).abs ≤ (16 * c * c) / (n - 1) := by
  have nPositive : 0 < n := by grind
  have nSubPositive : 0 < n - 1 := by grind
  have positiveCount := Rat.mul_pos nPositive nSubPositive
  have first := renormalized_deletion_bound _ _ _ _ _ positiveCount countLower
    retainedLower retainedUpper deletedLower deletedUpper
  apply Rat.le_trans first
  have boundNonneg : 0 ≤ 2 * (4 * c * c) := by grind
  have scaled := Rat.mul_le_mul_of_nonneg_left countUpper boundNonneg
  apply Rat.le_of_mul_le_mul_right _ positiveCount
  rw [Rat.div_mul_cancel (Rat.ne_of_gt positiveCount), Rat.mul_comm n (n - 1),
    ← Rat.mul_assoc (16 * c * c / (n - 1)) (n - 1) n,
    Rat.div_mul_cancel (Rat.ne_of_gt nSubPositive)]
  grind

/-- The published constant cannot be inferred from the scalar hypotheses
alone. This example uses signed bounded terms and is a scalar calculation. -/
theorem original_constant_fails_for_bounded_terms :
    (((12 : Rat) - 8) * (-4) + 32) / 12 - (-4) > 8 / 3 ∧
      (((12 : Rat) - 8) * (-4) + 32) / 12 - (-4) = 16 / 3 := by decide +kernel

def strictUpperTail (observed : Rat) (reference : List Rat) : Rat :=
  ((reference.countP fun x => decide (observed < x) : Nat) : Rat) / reference.length

def correctedUpperTail (observed : Rat) (reference : List Rat) : Rat :=
  ((1 + (reference.countP fun x => decide (observed ≤ x) : Nat) : Nat) : Rat) /
    (1 + (reference.length : Rat))

/-- For constant data, centering gives an observed statistic and reference
values all equal to zero. Ties and the finite correction give p = 1. -/
theorem constant_data_tail (b : Nat) :
    strictUpperTail 0 (List.replicate b 0) = 0 ∧
      correctedUpperTail 0 (List.replicate b 0) = 1 := by
  simp [strictUpperTail, correctedUpperTail, List.countP_replicate]
  have positive : 0 < 1 + (b : Rat) := by grind
  refine ⟨?_, Rat.mul_inv_cancel _ (Rat.ne_of_gt positive)⟩
  simp [Rat.div_def]

end

end OpenCausalScience.Papers.LeeHonavar2017.DeletionBound

module
public import Std

/-!
# Lee and Bareinboim (2021), left inversion on the target support

Theorem 1, Appendix C, Equations (5)–(7) and (11) of the October 2026
correction. Once the three observable vectors have the stipulated common
proxy factorization, a left inverse recovers the numerator, denominator and
target latent weight. The algebra uses the left inverse as a hypothesis.
A concrete rational stochastic proxy with three rows and two columns supplies
a worked rectangular instance.
-/

namespace OpenCausalScience.Papers.LeeBareinboim2021.ProxyInversion

@[expose] public section

/-- A supported term in the final adjustment sum. Zero-weight latent states
contribute zero without evaluation of an unsupported conditional. -/
def adjustmentTerm (joint observedWeight targetWeight : Rat) : Rat :=
  if targetWeight = 0 then 0 else (joint / observedWeight) * targetWeight

/-- Left inversion followed by support-restricted division reconstructs the
weighted response law term whenever the stated overlap holds. -/
theorem recover_adjustment_term {U W : Type}
    (mix : (U → Rat) → W → Rat) (invert : (W → Rat) → U → Rat)
    (leftInverse : ∀ v, invert (mix v) = v)
    (response observedWeight targetWeight : U → Rat)
    (yProxy xProxy targetProxy : W → Rat)
    (yFactor : yProxy = mix (fun u => response u * observedWeight u))
    (xFactor : xProxy = mix observedWeight)
    (targetFactor : targetProxy = mix targetWeight)
    (overlap : ∀ u, targetWeight u ≠ 0 → 0 < observedWeight u)
    (u : U) :
    adjustmentTerm (invert yProxy u) (invert xProxy u) (invert targetProxy u) =
      response u * targetWeight u := by
  rw [yFactor, xFactor, targetFactor, leftInverse, leftInverse, leftInverse]
  by_cases hz : targetWeight u = 0
  · simp [adjustmentTerm, hz]
  · simp [adjustmentTerm, hz, Rat.mul_div_cancel (Rat.ne_of_gt (overlap u hz))]

/-- A full-column-rank stochastic proxy indexed by two latent states and three
proxy values. Its first two rows are already invertible. -/
def rectangularProxy (v : Bool → Rat) (w : Fin 3) : Rat :=
  if w = 0 then v false / 2 + v true / 4
  else if w = 1 then v false / 4 + v true / 2
  else v false / 4 + v true / 4

/-- Left inverse obtained from the first two rows. The reconstruction argument
applies to any left inverse on the image, including the Moore–Penrose one
when full column rank is established. -/
def rectangularLeft (v : Fin 3 → Rat) (u : Bool) : Rat :=
  if u then (8 * v 1 - 4 * v 0) / 3 else (8 * v 0 - 4 * v 1) / 3

theorem rectangular_proxy_left_inverse (v : Bool → Rat) :
    rectangularLeft (rectangularProxy v) = v := by
  funext u
  cases u <;> simp [rectangularLeft, rectangularProxy] <;> grind

/-- Applying the inversion to a rectangular proxy can yield a target law
supported on only one latent state, even though the original proxy keeps both
columns. -/
theorem zero_weight_rectangular_recovery :
    adjustmentTerm (rectangularLeft (rectangularProxy (fun u => if u then 0 else 1 / 4)) false)
      (rectangularLeft (rectangularProxy (fun u => if u then 0 else 1)) false)
      (rectangularLeft (rectangularProxy (fun u => if u then 0 else 1)) false) = 1 / 4 ∧
    adjustmentTerm (rectangularLeft (rectangularProxy (fun u => if u then 0 else 1 / 4)) true)
      (rectangularLeft (rectangularProxy (fun u => if u then 0 else 1)) true)
      (rectangularLeft (rectangularProxy (fun u => if u then 0 else 1)) true) = 0 := by
  simp only [rectangular_proxy_left_inverse]
  decide +kernel

end

end OpenCausalScience.Papers.LeeBareinboim2021.ProxyInversion

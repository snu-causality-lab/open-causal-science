module
public import Std

/-! # The conditional formula in Figure 1(b)

The response factor involving the shared latent causes of `C` and `Y`
can be kept as a joint factor. Given the displayed factorization,
conditional observation of `A,M,C` normalizes only that shared factor.
The baseline mediator factor remains separate.
Source: https://proceedings.mlr.press/v89/malinsky19b/malinsky19b.pdf#page=8
-/

namespace OpenCausalScience.Papers.MalinskyEtAl2019.Figure1BFormula

@[expose] public section

def sumBinary (f : Bool → Rat) : Rat := f false + f true

/-- Factorization after summing out the latent cause of `C` and `Y`.
The arguments to `shared` are `C`, the copies of `A` and `M` read by
`Y`, and `Y`. The arguments to `mediator` are `C`, `A`, and `M`. -/
structure Factors where
  covariate : Bool → Rat
  treatment : Bool → Bool → Rat
  mediator : Bool → Bool → Bool → Rat
  shared : Bool → Bool → Bool → Bool → Rat
  mediator_normalized : ∀ c a, sumBinary (mediator c a) = 1
  shared_normalized : ∀ c a m, sumBinary (shared c a m) = covariate c

def observedCell (f : Factors) (c a m y : Bool) : Rat :=
  (f.treatment c a * f.mediator c a m) * f.shared c a m y

def observedOutcome (f : Factors) (c a m y : Bool) : Rat :=
  observedCell f c a m y / sumBinary (observedCell f c a m)

def observedMediator (f : Factors) (c a m : Bool) : Rat :=
  sumBinary (observedCell f c a m) / sumBinary (fun m => sumBinary (observedCell f c a m))

def pathJoint (f : Factors) (c active baseline y : Bool) : Rat :=
  sumBinary fun m => f.mediator c baseline m * f.shared c active m y

def pathConditional (f : Factors) (c active baseline y : Bool) : Rat :=
  pathJoint f c active baseline y / sumBinary (pathJoint f c active baseline)

private theorem sum_binary_mul_left (a : Rat) (b : Bool → Rat) :
    sumBinary (fun x => a * b x) = a * sumBinary b := by
  simp only [sumBinary, Rat.mul_add]

private theorem sum_binary_mul_right (a : Bool → Rat) (b : Rat) :
    sumBinary (fun x => a x * b) = sumBinary a * b := by
  simp only [sumBinary, Rat.add_mul]

private theorem mul_div_mul (a b c : Rat) (ha : a ≠ 0) : (a * b) / (a * c) = b / c := by
  by_cases hc : c = 0
  · simp [hc, Rat.mul_zero, Rat.div_def]
  · have hz : a * c ≠ 0 := by
      intro zero
      have eq : a⁻¹ * (a * c) = c := by
        rw [← Rat.mul_assoc, Rat.inv_mul_cancel a ha, Rat.one_mul]
      rw [zero, Rat.mul_zero] at eq
      exact hc eq.symm
    have same : ((a * b) / (a * c)) * (a * c) = (b / c) * (a * c) := by
      rw [Rat.div_mul_cancel hz, Rat.mul_comm a c, ← Rat.mul_assoc, Rat.div_mul_cancel hc, Rat.mul_comm b a]
    have cancel (t : Rat) : t * (a * c) * (a * c)⁻¹ = t := by
      rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hz, Rat.mul_one]
    exact (cancel _).symm.trans ((congrArg (· * (a * c)⁻¹) same).trans (cancel _))

private theorem marginalize_y (f : Factors) (c a m : Bool) :
    sumBinary (observedCell f c a m) = (f.treatment c a * f.mediator c a m) * f.covariate c := by
  unfold observedCell
  rw [sum_binary_mul_left, f.shared_normalized]

private theorem outcome (f : Factors) (c a m y : Bool)
    (support : f.treatment c a * f.mediator c a m ≠ 0) :
    observedOutcome f c a m y = f.shared c a m y / f.covariate c := by
  rw [observedOutcome, marginalize_y, observedCell]
  exact mul_div_mul _ _ _ support

private theorem mediator (f : Factors) (c a m : Bool)
    (support : f.treatment c a * f.covariate c ≠ 0) :
    observedMediator f c a m = f.mediator c a m := by
  rw [observedMediator, marginalize_y]
  have rearrange (b : Bool) : (f.treatment c a * f.mediator c a b) * f.covariate c =
      (f.treatment c a * f.covariate c) * f.mediator c a b := by
    rw [Rat.mul_assoc, Rat.mul_comm (f.mediator c a b), ← Rat.mul_assoc]
  have each : (fun b => sumBinary (observedCell f c a b)) =
      fun b => (f.treatment c a * f.covariate c) * f.mediator c a b :=
    funext fun b => (marginalize_y f c a b).trans (rearrange b)
  rw [rearrange, each, sum_binary_mul_left, f.mediator_normalized, mul_div_mul _ _ _ support]
  have invOne : (1 : Rat)⁻¹ = 1 := by decide +kernel
  rw [Rat.div_def, invOne, Rat.mul_one]

/-- The total mass of a baseline mediator mixed with the outcome
factor on `C` is the unchanged mass of that covariate cell. -/
theorem path_evidence_eq_covariate (f : Factors) (c active baseline : Bool) :
    sumBinary (pathJoint f c active baseline) = f.covariate c := by
  have commute (x : Bool → Bool → Rat) :
      sumBinary (fun i => sumBinary (fun j => x i j)) =
        sumBinary (fun j => sumBinary (fun i => x i j)) := by
    change (x false false + x false true) + (x true false + x true true) =
      (x false false + x true false) + (x false true + x true true)
    have middle (a b c : Rat) : a + (b + c) = b + (a + c) := by
      rw [← Rat.add_assoc, Rat.add_comm a b, Rat.add_assoc]
    rw [Rat.add_assoc, middle (x false true), ← Rat.add_assoc]
  unfold pathJoint
  rw [commute]
  have each : (fun m => sumBinary fun y => f.mediator c baseline m * f.shared c active m y) =
      fun m => f.mediator c baseline m * f.covariate c := by
    funext m
    rw [sum_binary_mul_left, f.shared_normalized]
  rw [each, sum_binary_mul_right, f.mediator_normalized, Rat.one_mul]

/-- Reconstruct the paper's conditional estimand from observed
conditionals on supported parent cells. -/
theorem conditional_path_formula (f : Factors) (c active baseline y : Bool)
    (baselineSupport : f.treatment c baseline * f.covariate c ≠ 0)
    (outcomeSupport : ∀ m, f.treatment c active * f.mediator c active m ≠ 0) :
    pathConditional f c active baseline y =
      sumBinary fun m => observedOutcome f c active m y * observedMediator f c baseline m := by
  rw [pathConditional, path_evidence_eq_covariate, pathJoint, Rat.div_def, ← sum_binary_mul_right]
  apply congrArg sumBinary
  funext m
  rw [outcome f c active m y (outcomeSupport m), mediator f c baseline m baselineSupport, Rat.div_def]
  rw [Rat.mul_assoc, Rat.mul_comm (f.mediator c baseline m)]

end
end OpenCausalScience.Papers.MalinskyEtAl2019.Figure1BFormula

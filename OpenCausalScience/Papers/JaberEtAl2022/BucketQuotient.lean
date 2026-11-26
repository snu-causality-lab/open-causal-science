module
public import Std

/-! # The probability calculation for a bucket removal

Jaber, Ribeiro, Zhang and Bareinboim (2022), R-86, Proposition 2,
Equation (1). Assume the distribution before the bucket removal
factors into the intervention-specific kernel after removal and a
normalized mechanism for the bucket. The bucket's mechanism depends
on other variables only through the denominator's conditioning
value. The marginal of these conditioning variables is unchanged
across interventions on the bucket. Summing the old kernel computes
the mechanism, and dividing retrieves the new kernel on supported cells.

The proof in Appendix D supplies these restrictions from the PAG
condition. That implication is separate here.
Source: https://causalai.net/r86.pdf#page=6
-/

namespace OpenCausalScience.Papers.JaberEtAl2022.BucketQuotient

@[expose] public section

variable {B Rest Fixed : Type} [DecidableEq Fixed]

def bucketAndCondition (states : List Rest) (project : Rest → Fixed)
    (joint : B → Rest → Rat) (bucket : B) (context : Fixed) : Rat :=
  (states.map fun rest => if project rest = context then joint bucket rest else 0).sum

def bucketConditional (buckets : List B) (states : List Rest) (project : Rest → Fixed)
    (joint : B → Rest → Rat) (bucket : B) (context : Fixed) : Rat :=
  bucketAndCondition states project joint bucket context /
    (buckets.map fun b => bucketAndCondition states project joint b context).sum

def conditionMass (states : List Rest) (project : Rest → Fixed) (retained : Rest → Rat)
    (context : Fixed) : Rat :=
  (states.map fun rest => if project rest = context then retained rest else 0).sum

private theorem sum_scale_left {A : Type} (as : List A) (f : A → Rat) (c : Rat) :
    (as.map fun a => c * f a).sum = c * (as.map f).sum := by
  induction as with
  | nil => simp [Rat.mul_zero]
  | cons a rest ih => simp [ih, Rat.mul_add]

private theorem sum_scale_right {A : Type} (as : List A) (f : A → Rat) (c : Rat) :
    (as.map fun a => f a * c).sum = (as.map f).sum * c := by
  induction as with
  | nil => simp [Rat.zero_mul]
  | cons a rest ih => simp [ih, Rat.add_mul]

theorem bucket_and_condition_eq (states : List Rest) (project : Rest → Fixed)
    (old retained : B → Rest → Rat) (mechanism : Fixed → B → Rat)
    (factor : ∀ b r, old b r = mechanism (project r) b * retained b r)
    (bucket : B) (context : Fixed) :
    bucketAndCondition states project old bucket context =
      mechanism context bucket * conditionMass states project (retained bucket) context := by
  unfold bucketAndCondition conditionMass
  rw [← sum_scale_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r _
  by_cases equal : project r = context
  · simp [equal, factor]
  · simp [equal, Rat.mul_zero]

theorem bucket_conditional_eq_mechanism (buckets : List B) (states : List Rest)
    (project : Rest → Fixed) (old retained : B → Rest → Rat)
    (mechanism : Fixed → B → Rat) (baseline : Fixed → Rat)
    (factor : ∀ b r, old b r = mechanism (project r) b * retained b r)
    (unchanged : ∀ b context, conditionMass states project (retained b) context = baseline context)
    (normalized : ∀ context, (buckets.map (mechanism context)).sum = 1)
    (bucket : B) (context : Fixed) (support : baseline context ≠ 0) :
    bucketConditional buckets states project old bucket context = mechanism context bucket := by
  have marginal (b : B) : bucketAndCondition states project old b context =
      mechanism context b * baseline context := by
    rw [bucket_and_condition_eq states project old retained mechanism factor b context, unchanged]
  unfold bucketConditional
  rw [marginal, List.map_congr_left (fun b _ => marginal b), sum_scale_right, normalized,
    Rat.one_mul, Rat.mul_div_cancel support]

/-- The actual conditional in the quotient is computed from the old
kernel. The two support hypotheses license that conditional and the
final division. -/
theorem bucket_quotient_recovers_kernel (buckets : List B) (states : List Rest)
    (project : Rest → Fixed) (old retained : B → Rest → Rat)
    (mechanism : Fixed → B → Rat) (baseline : Fixed → Rat)
    (factor : ∀ b r, old b r = mechanism (project r) b * retained b r)
    (unchanged : ∀ b context, conditionMass states project (retained b) context = baseline context)
    (normalized : ∀ context, (buckets.map (mechanism context)).sum = 1)
    (bucket : B) (rest : Rest)
    (conditionSupport : baseline (project rest) ≠ 0)
    (bucketSupport : mechanism (project rest) bucket ≠ 0) :
    old bucket rest / bucketConditional buckets states project old bucket (project rest) =
      retained bucket rest := by
  rw [bucket_conditional_eq_mechanism buckets states project old retained mechanism baseline factor
    unchanged normalized bucket (project rest) conditionSupport, factor, Rat.mul_comm,
    Rat.mul_div_cancel bucketSupport]

end

end OpenCausalScience.Papers.JaberEtAl2022.BucketQuotient

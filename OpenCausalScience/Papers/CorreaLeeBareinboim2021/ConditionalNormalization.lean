module
public import OpenCausalScience.Papers.CorreaLeeBareinboim2021.Unnesting

/-! # Normalizing a supported conditional query

Correa, Lee and Bareinboim (2021), equation (23) and Algorithm 2,
line 4. If the joint and evidence masses share the same nonzero factor,
it cancels. The factorization and support are premises here.

Source: https://proceedings.neurips.cc/paper/2021/file/36bedb6eb7152f39b16328448942822b-Paper.pdf#page=9
-/

namespace OpenCausalScience.Papers.CorreaLeeBareinboim2021.ConditionalNormalization

open TianPearl2003.AncestralMarginal (mass)
open Unnesting (IdentifiedBy)

@[expose] public section

def conditionalOn (joint evidence : Rat) : Option Rat :=
  if 0 < evidence then some (joint / evidence) else none

theorem conditional_on_unsupported {joint evidence : Rat} (unsupported : ¬ 0 < evidence) :
    conditionalOn joint evidence = none := by
  simp [conditionalOn, unsupported]

/-- A common evidence factor can be canceled at positive evidence.
The retained denominator must itself have positive mass. -/
theorem conditional_on_common_factor (joint evidence factor : Rat)
    (supported : 0 < evidence) (factorPositive : 0 < factor) :
    conditionalOn (joint * factor) (evidence * factor) = conditionalOn joint evidence := by
  have positive : 0 < evidence * factor := Rat.mul_pos supported factorPositive
  simp only [conditionalOn, ite_eq_left positive, ite_eq_left supported, Option.some.injEq]
  have before : (joint / evidence) * (evidence * factor) = joint * factor := by
    rw [← Rat.mul_assoc, Rat.div_mul_cancel (Rat.ne_of_gt supported)]
  rw [← before, Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel _ (Rat.ne_of_gt positive),
    Rat.mul_one]

/-- The selected joint and evidence identify the conditional on the
domain where it is defined. -/
theorem conditional_on_identified {Model Sources : Type} (data : Model → Sources)
    (joint evidence : Model → Rat)
    (positive : ∀ m, 0 < evidence m)
    (jointIdentified : IdentifiedBy data joint)
    (evidenceIdentified : IdentifiedBy data evidence) :
    IdentifiedBy data (fun m => joint m / evidence m) ∧
      ∀ m, conditionalOn (joint m) (evidence m) = some (joint m / evidence m) := by
  constructor
  · intro first second sameSources
    dsimp only
    rw [jointIdentified first second sameSources, evidenceIdentified first second sameSources]
  · intro m
    simp [conditionalOn, positive m]

/-- The numerator event can be replaced by a different pointwise
description on the given evidence, with the denominator unchanged. -/
theorem conditional_on_event_congr {Ω : Type} (atoms : List Ω) (weight : Ω → Rat)
    (first second evidence : Ω → Bool)
    (agree : ∀ unit, evidence unit = true → first unit = second unit) :
    conditionalOn (mass atoms weight (fun unit => first unit && evidence unit))
        (mass atoms weight evidence) =
      conditionalOn (mass atoms weight (fun unit => second unit && evidence unit))
        (mass atoms weight evidence) := by
  have same : (fun unit => first unit && evidence unit) =
      (fun unit => second unit && evidence unit) := by
    funext unit
    cases h : evidence unit
    · simp
    · simp [agree unit h]
  rw [same]

end
end OpenCausalScience.Papers.CorreaLeeBareinboim2021.ConditionalNormalization

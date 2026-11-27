module
public import OpenCausalScience.Probability.FiniteSummation

/-! # Gluing compatible finite clique marginals

The two marginals agree on their common separator. On each supported
separator cell their normalized product recovers both marginals.
An unsupported separator cell receives zero joint mass.
-/

namespace OpenCausalScience.Papers.LauritzenSpiegelhalter1988.SeparatorGluing

open Probability.FiniteSummation

@[expose] public section

variable {A B : Type}

private theorem sum_nonnegative (states : List A) (f : A → Rat)
    (nonnegative : ∀ x ∈ states, 0 ≤ f x) : 0 ≤ sumOver states f := by
  induction states with
  | nil => exact Rat.le_refl
  | cons first rest ih =>
    exact Rat.add_nonneg (nonnegative first List.mem_cons_self)
      (ih (fun x there => nonnegative x (List.mem_cons_of_mem _ there)))

private theorem summand_le (states : List A) (f : A → Rat)
    (nonnegative : ∀ x ∈ states, 0 ≤ f x) {a : A} (member : a ∈ states) :
    f a ≤ sumOver states f := by
  induction states with
  | nil => cases member
  | cons first rest ih =>
    have headWeight := nonnegative first List.mem_cons_self
    have tailWeights : ∀ x ∈ rest, 0 ≤ f x :=
      fun x there => nonnegative x (List.mem_cons_of_mem _ there)
    change f a ≤ f first + sumOver rest f
    rcases List.mem_cons.mp member with rfl | there
    · have tailWeight := sum_nonnegative rest f tailWeights
      grind
    · have bound := ih tailWeights there
      grind

def glue (separator left right : Rat) : Rat :=
  if separator = 0 then 0 else left * right / separator

/-- The calculation in one separator cell. Equality of the supplied
separator marginals is the compatibility premise. -/
theorem recover_left (left : List A) (right : List B) (f : A → Rat) (g : B → Rat)
    (nonnegative : ∀ x ∈ left, 0 ≤ f x)
    (agree : sumOver left f = sumOver right g) {a : A} (member : a ∈ left) :
    sumOver right (fun b => glue (sumOver left f) (f a) (g b)) = f a := by
  by_cases zero : sumOver left f = 0
  · have bound := summand_le left f nonnegative member
    rw [zero] at bound
    have aZero := Rat.le_antisymm bound (nonnegative a member)
    simp only [glue, zero, ite_true, aZero]
    have scale := sum_mul_left right g 0
    simpa only [Rat.zero_mul] using scale
  · simp only [glue, zero, ite_false, Rat.div_def]
    rw [sum_mul_right, sum_mul_left, ← agree, Rat.mul_assoc,
      Rat.mul_inv_cancel _ zero, Rat.mul_one]

theorem compatible_cell_marginals (left : List A) (right : List B)
    (f : A → Rat) (g : B → Rat)
    (leftNonnegative : ∀ a ∈ left, 0 ≤ f a)
    (rightNonnegative : ∀ b ∈ right, 0 ≤ g b)
    (agree : sumOver left f = sumOver right g) :
    (∀ a ∈ left, sumOver right (fun b => glue (sumOver left f) (f a) (g b)) = f a) ∧
    (∀ b ∈ right, sumOver left (fun a => glue (sumOver left f) (f a) (g b)) = g b) := by
  constructor
  · intro a member
    apply recover_left left right f g leftNonnegative agree member
  · intro b member
    have swapped := recover_left right left g f rightNonnegative agree.symm member
    simpa only [glue, ← agree, Rat.mul_comm (g b)] using swapped

end
end OpenCausalScience.Papers.LauritzenSpiegelhalter1988.SeparatorGluing

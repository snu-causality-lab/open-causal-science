module
public import Std

/-! Finite sums and products of rational cells, with explicit multiplicity. -/

namespace OpenCausalScience.Probability.FiniteSummation

@[expose] public section

variable {A B : Type}

def sumOver (values : List A) (term : A → Rat) : Rat := (values.map term).sum

def productOver (values : List A) (term : A → Rat) : Rat :=
  values.foldr (fun x value => term x * value) 1

theorem sum_congr (values : List A) (first second : A → Rat)
    (agree : ∀ x ∈ values, first x = second x) :
    sumOver values first = sumOver values second :=
  congrArg List.sum (List.map_congr_left agree)

theorem sum_map (values : List A) (encode : A → B) (term : B → Rat) :
    sumOver (values.map encode) term = sumOver values (fun x => term (encode x)) := by
  simp only [sumOver, List.map_map, Function.comp_def]

theorem sum_mul_left (values : List A) (term : A → Rat) (scale : Rat) :
    sumOver values (fun x => scale * term x) = scale * sumOver values term := by
  induction values with
  | nil => simp [sumOver, Rat.mul_zero]
  | cons x rest ih => simp [sumOver, Rat.mul_add] at ih ⊢; rw [ih]

theorem sum_mul_right (values : List A) (term : A → Rat) (scale : Rat) :
    sumOver values (fun x => term x * scale) = sumOver values term * scale := by
  simp only [Rat.mul_comm _ scale]
  exact sum_mul_left values term scale

theorem sum_append (first second : List A) (term : A → Rat) :
    sumOver (first ++ second) term = sumOver first term + sumOver second term := by
  -- Rational addition has the required identity and associativity.
  induction first with
  | nil => simp [sumOver, Rat.zero_add]
  | cons x rest ih =>
    simp only [List.cons_append, sumOver, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Rat.add_assoc]

theorem sum_flatMap (values : List A) (choices : A → List B) (term : B → Rat) :
    sumOver (values.flatMap choices) term =
      sumOver values (fun value => sumOver (choices value) term) := by
  induction values with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.flatMap_cons, sum_append, ih]
    rfl

theorem sum_product (left : List A) (right : List B) (f : A → Rat) (g : B → Rat) :
    sumOver left (fun x => sumOver right (fun y => f x * g y)) =
      sumOver left f * sumOver right g := by
  simp only [sum_mul_left, sum_mul_right]

theorem product_congr (values : List A) (first second : A → Rat)
    (agree : ∀ x ∈ values, first x = second x) :
    productOver values first = productOver values second := by
  induction values with
  | nil => rfl
  | cons x rest ih =>
    change first x * productOver rest first = second x * productOver rest second
    rw [agree x List.mem_cons_self, ih (fun y member => agree y (List.mem_cons_of_mem _ member))]

theorem product_append (first second : List A) (term : A → Rat) :
    productOver (first ++ second) term = productOver first term * productOver second term := by
  induction first with
  | nil => simp [productOver, Rat.one_mul]
  | cons x rest ih =>
    change term x * productOver (rest ++ second) term =
      (term x * productOver rest term) * productOver second term
    rw [ih, Rat.mul_assoc]

theorem product_partition (values : List A) (left : A → Bool) (term : A → Rat) :
    productOver values term =
      productOver (values.filter left) term * productOver (values.filter (fun x => !left x)) term := by
  induction values with
  | nil => exact (Rat.one_mul 1).symm
  | cons x rest ih =>
    cases which : left x
    · simp only [List.filter_cons, which, Bool.false_eq_true, ite_false, Bool.not_false,
        ite_true]
      change term x * productOver rest term =
        productOver (rest.filter left) term *
          (term x * productOver (rest.filter fun y => !left y) term)
      rw [ih, ← Rat.mul_assoc (productOver (rest.filter left) term) (term x),
        Rat.mul_comm (productOver (rest.filter left) term) (term x), Rat.mul_assoc]
    · simp only [List.filter_cons, which, ite_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change term x * productOver rest term =
        (term x * productOver (rest.filter left) term) *
          productOver (rest.filter fun y => !left y) term
      rw [ih, Rat.mul_assoc]

end
end OpenCausalScience.Probability.FiniteSummation

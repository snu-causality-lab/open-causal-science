module
public import Std

/-!
# Hwang et al. (2024), supported Rule 3

This module checks the probability argument of Lemma 4.1, Rule 3, in
Appendix E of the 2026-09-20 correction. The mass function comes from a
finite exogenous law and uniform intervention-indicator assignments.
The graph steps supplying conditional independence in the augmented model
remain an explicit premise.

Source: https://www.sanghacklee.me/ai-corrected/positivity_AI_corrected_2026-09-20.pdf
-/

namespace OpenCausalScience.Papers.HwangEtAl2024Positivity.SupportedRuleThree

@[expose] public section

/-- Encode the binary indicator vector by its integer value. The extreme
values correspond to the all-zero and all-one vectors in Appendix E. -/
abbrev Indicators (n : Nat) := Fin (2 ^ n)

theorem indicator_count_positive (n : Nat) : 0 < 2 ^ n := by
  exact Nat.pow_pos (by decide)

def allOff (n : Nat) : Indicators n := ⟨0, indicator_count_positive n⟩

def allOn (n : Nat) : Indicators n :=
  ⟨2 ^ n - 1, Nat.sub_lt (indicator_count_positive n) (by decide)⟩

/-- Under independent fair indicators, every vector has this probability. -/
def indicatorMass (n : Nat) : Rat := ((2 ^ n : Nat) : Rat)⁻¹

theorem indicator_mass_positive (n : Nat) : 0 < indicatorMass n :=
  Rat.inv_pos.mpr (Rat.natCast_pos.mpr (indicator_count_positive n))

/-- The response pair is the outcome and conditioning value in the acyclic
model with `X` already set to `x`. For a given indicator vector, each
indicated equation in `Z` is replaced by its fixed intervention value.
The response function gives the resulting unique solution at an exogenous
atom. Its all-off and all-on fibers give `Pₓ` and `Pₓ,𝓏`, respectively. -/
structure AugmentedModel (n : Nat) (Ω Y W : Type) where
  atoms : List Ω
  weight : Ω → Rat
  nonnegative : ∀ a ∈ atoms, 0 ≤ weight a
  normalized : (atoms.map weight).sum = 1
  response : Indicators n → Ω → Y × W

variable {n : Nat} {Ω Y W : Type}

def AugmentedModel.regimeMass (model : AugmentedModel n Ω Y W) (i : Indicators n)
    (event : Y × W → Bool) : Rat :=
  (model.atoms.map fun a => if event (model.response i a) then model.weight a else 0).sum

/-- The mass of `event` together with `I = i` in the augmented law. -/
def AugmentedModel.sliceMass (model : AugmentedModel n Ω Y W) (i : Indicators n)
    (event : Y × W → Bool) : Rat :=
  model.regimeMass i event * indicatorMass n

/-- The marginal event mass in the augmented law, summing out indicators. -/
def AugmentedModel.mass (model : AugmentedModel n Ω Y W) (event : Y × W → Bool) : Rat :=
  ((List.finRange (2 ^ n)).map fun i => model.sliceMass i event).sum

private theorem sum_constant {A : Type} (values : List A) (c : Rat) :
    (values.map fun _ => c).sum = (values.length : Rat) * c := by
  induction values with
  | nil => simp
  | cons a values ih =>
    have oneCast : ((1 : Nat) : Rat) = 1 := rfl
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Rat.natCast_add,
      Rat.add_mul, oneCast, Rat.one_mul, Rat.add_comm]

theorem AugmentedModel.mass_univ (model : AugmentedModel n Ω Y W) :
    model.mass (fun _ => true) = 1 := by
  have each (i : Indicators n) : model.sliceMass i (fun _ => true) = indicatorMass n := by
    simp [AugmentedModel.sliceMass, AugmentedModel.regimeMass, model.normalized, Rat.one_mul]
  simp only [AugmentedModel.mass, each, sum_constant, List.length_finRange, indicatorMass]
  exact Rat.mul_inv_cancel _ (Rat.ne_of_gt (Rat.natCast_pos.mpr (indicator_count_positive n)))

private theorem sum_map_nonneg {A : Type} (values : List A) (f : A → Rat)
    (nonnegative : ∀ a ∈ values, 0 ≤ f a) : 0 ≤ (values.map f).sum := by
  induction values with
  | nil => exact Rat.le_refl
  | cons a values ih =>
    exact Rat.add_nonneg (nonnegative a (by simp))
      (ih (fun b hb => nonnegative b (by simp [hb])))

private theorem value_le_sum {A : Type} (values : List A) (f : A → Rat)
    (nonnegative : ∀ a ∈ values, 0 ≤ f a) {a : A} (present : a ∈ values) :
    f a ≤ (values.map f).sum := by
  induction values with
  | nil => simp at present
  | cons b values ih =>
    have rest (x : A) (hx : x ∈ values) := nonnegative x (by simp [hx])
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp present with rfl | present
    · simpa only [Rat.add_zero] using
        (Rat.add_le_add_left.mpr (sum_map_nonneg values f rest) :
          f a + 0 ≤ f a + (values.map f).sum)
    · refine Rat.le_trans (ih rest present) ?_
      simpa only [Rat.zero_add] using
        (Rat.add_le_add_right.mpr (nonnegative b (by simp)) :
          0 + (values.map f).sum ≤ f b + (values.map f).sum)

theorem AugmentedModel.regime_mass_nonnegative (model : AugmentedModel n Ω Y W)
    (i : Indicators n) (event : Y × W → Bool) : 0 ≤ model.regimeMass i event := by
  apply sum_map_nonneg
  intro a member
  split <;> first | exact model.nonnegative a member | exact Rat.le_refl

theorem AugmentedModel.slice_mass_positive (model : AugmentedModel n Ω Y W)
    (i : Indicators n) (event : Y × W → Bool) :
    0 < model.sliceMass i event ↔ 0 < model.regimeMass i event :=
  Rat.mul_pos_iff_of_pos_right (indicator_mass_positive n)

theorem AugmentedModel.slice_mass_le_mass (model : AugmentedModel n Ω Y W)
    (i : Indicators n) (event : Y × W → Bool) : model.sliceMass i event ≤ model.mass event := by
  apply value_le_sum _ _ _ (List.mem_finRange i)
  intro j _
  exact Rat.mul_nonneg (model.regime_mass_nonnegative j event)
    (Rat.le_of_lt (indicator_mass_positive n))

private theorem cancel_indicator (a b probability : Rat) (positive : 0 < probability) :
    (a * probability) / (b * probability) = a / b := by
  rw [Rat.div_def (a * probability), Rat.inv_mul_rev, Rat.div_def, Rat.mul_assoc,
    ← Rat.mul_assoc probability, Rat.mul_inv_cancel _ (Rat.ne_of_gt positive), Rat.one_mul]

private theorem divide_cross_product (a b c d : Rat) (b_nonzero : b ≠ 0) (d_nonzero : d ≠ 0)
    (equal : a * d = c * b) : a / b = c / d := by
  have right : c * b / d = (c / d) * b := by
    simp only [Rat.div_def, Rat.mul_assoc, Rat.mul_comm b]
  have divided := congrArg (fun product => product / d / b) equal
  rwa [Rat.mul_div_cancel d_nonzero, right, Rat.mul_div_cancel b_nonzero] at divided

variable [DecidableEq Y] [DecidableEq W]

def conditioningEvent (w : W) (response : Y × W) : Bool := decide (response.2 = w)

def jointEvent (y : Y) (w : W) (response : Y × W) : Bool :=
  decide (response.1 = y ∧ response.2 = w)

def AugmentedModel.regimeConditional (model : AugmentedModel n Ω Y W)
    (i : Indicators n) (y : Y) (w : W) : Rat :=
  model.regimeMass i (jointEvent y w) / model.regimeMass i (conditioningEvent w)

def AugmentedModel.conditioningMass (model : AugmentedModel n Ω Y W)
    (i : Indicators n) (w : W) : Rat := model.regimeMass i (conditioningEvent w)

/-- The cross-product form of `I ⟂ Y | W` in the augmented law. It uses
the actual indicator slices and their sums, including mixed assignments. -/
def AugmentedModel.indicatorIndependent (model : AugmentedModel n Ω Y W)
    (y : Y) (w : W) : Prop := ∀ i,
  model.sliceMass i (jointEvent y w) * model.mass (conditioningEvent w) =
    model.mass (jointEvent y w) * model.sliceMass i (conditioningEvent w)

private theorem AugmentedModel.regime_eq_augmented (model : AugmentedModel n Ω Y W)
    (i : Indicators n) (y : Y) (w : W) (supported : 0 < model.conditioningMass i w)
    (independent : model.indicatorIndependent y w) :
    model.regimeConditional i y w = model.mass (jointEvent y w) / model.mass (conditioningEvent w) := by
  have slicePositive := (model.slice_mass_positive i (conditioningEvent w)).mpr supported
  have marginalPositive : 0 < model.mass (conditioningEvent w) := by
    rw [Rat.lt_iff_le_and_not_ge]
    exact ⟨Rat.le_trans (Rat.le_of_lt slicePositive) (model.slice_mass_le_mass i (conditioningEvent w)),
      fun impossible => (Rat.not_le.mpr slicePositive) <|
        Rat.le_trans (model.slice_mass_le_mass i (conditioningEvent w)) impossible⟩
  have slice := divide_cross_product _ _ _ _ (Rat.ne_of_gt slicePositive)
    (Rat.ne_of_gt marginalPositive) (independent i)
  unfold AugmentedModel.sliceMass at slice
  rw [cancel_indicator _ _ _ (indicator_mass_positive n)] at slice
  exact slice

/-- Rule 3 in a finite augmented model. Both intervention regimes provide a
positive conditioning mass. The two observed slices therefore equal the
same supported conditional of the augmented law. -/
theorem supported_rule_three (model : AugmentedModel n Ω Y W) (y : Y) (w : W)
    (off_positive : 0 < model.conditioningMass (allOff n) w)
    (on_positive : 0 < model.conditioningMass (allOn n) w)
    (independent : model.indicatorIndependent y w) :
    model.regimeConditional (allOn n) y w = model.regimeConditional (allOff n) y w :=
  (model.regime_eq_augmented (allOn n) y w on_positive independent).trans
    (model.regime_eq_augmented (allOff n) y w off_positive independent).symm

/-- With no conditioning variables, every regime has a normalized mass
function and the two support assumptions of Rule 3 follow automatically. -/
theorem unconditional_rule_three (model : AugmentedModel n Ω Y Unit) (y : Y)
    (independent : model.indicatorIndependent y ()) :
    model.regimeConditional (allOn n) y () = model.regimeConditional (allOff n) y () := by
  have positive (i : Indicators n) : 0 < model.conditioningMass i () := by
    simpa [AugmentedModel.conditioningMass, AugmentedModel.regimeMass, conditioningEvent,
      model.normalized] using (by decide : (0 : Rat) < 1)
  exact supported_rule_three model y () (positive _) (positive _) independent

/-- Ordered support requirements for the substitution argument of Corollary
E.1. Each equality to an observable expression is available only after its
earlier support requirements have been proved. -/
inductive SupportDerivation : List Rat → Prop where
  | empty : SupportDerivation []
  | add {earlier : List Rat} (target observable : Rat)
      (prior : SupportDerivation earlier)
      (identified : (∀ p ∈ earlier, 0 < p) → target = observable)
      (observable_positive : 0 < observable) : SupportDerivation (target :: earlier)

theorem SupportDerivation.all_positive {requirements : List Rat}
    (derivation : SupportDerivation requirements) : ∀ p ∈ requirements, 0 < p := by
  induction derivation with
  | empty => simp
  | add target observable prior identified observable_positive ih =>
    intro p member
    rcases List.mem_cons.mp member with rfl | earlier
    · rwa [identified ih]
    · exact ih p earlier

end

end OpenCausalScience.Papers.HwangEtAl2024Positivity.SupportedRuleThree

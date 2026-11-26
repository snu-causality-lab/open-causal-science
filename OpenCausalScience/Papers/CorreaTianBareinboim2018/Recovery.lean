module
public import Std

/-! # Computing the adjustment expression from its sources

Correa, Tian and Bareinboim (2018), Definition 7 and equation (6).
At a fixed treatment and outcome, evaluate the adjustment formula
using the selected joint table and the same-population unselected
margin on the externally measured part of the adjustment set.
Source: https://causalai.net/r29.pdf#page=4
-/

namespace OpenCausalScience.Papers.CorreaTianBareinboim2018.Recovery

@[expose] public section

variable {A B X Y T R : Type}

def sumOver (values : List A) (f : A → Rat) : Rat := (values.map f).sum

theorem sum_congr (values : List A) (f g : A → Rat)
    (equal : ∀ a ∈ values, f a = g a) : sumOver values f = sumOver values g :=
  congrArg List.sum (List.map_congr_left equal)

theorem sum_mul_right (values : List A) (f : A → Rat) (c : Rat) :
    sumOver values (fun a => f a * c) = sumOver values f * c := by
  induction values with
  | nil => simp [sumOver, Rat.zero_mul]
  | cons a rest ih =>
    change f a * c + sumOver rest (fun x => f x * c) = (f a + sumOver rest f) * c
    rw [ih, Rat.add_mul]

private theorem sum_add (values : List A) (f g : A → Rat) :
    sumOver values (fun a => f a + g a) = sumOver values f + sumOver values g := by
  induction values with
  | nil => simp [sumOver, Rat.zero_add]
  | cons a rest ih =>
    change (f a + g a) + sumOver rest (fun x => f x + g x) =
      (f a + sumOver rest f) + (g a + sumOver rest g)
    rw [ih]
    ac_rfl

theorem sum_swap (left : List A) (right : List B) (f : A → B → Rat) :
    sumOver left (fun a => sumOver right (f a)) =
      sumOver right (fun b => sumOver left (fun a => f a b)) := by
  induction left with
  | nil =>
    change (0 : Rat) = sumOver right (fun _ => 0)
    induction right with
    | nil => rfl
    | cons b rest ih =>
      change (0 : Rat) = 0 + sumOver rest (fun _ => 0)
      rw [Rat.zero_add, ← ih]
  | cons a rest ih =>
    change sumOver right (f a) + sumOver rest (fun z => sumOver right (f z)) =
      sumOver right (fun b => f a b + sumOver rest (fun z => f z b))
    rw [ih, sum_add]

theorem sum_flat_map (left : List A) (right : A → List B) (f : B → Rat) :
    sumOver (left.flatMap right) f = sumOver left (fun a => sumOver (right a) f) := by
  induction left with
  | nil => rfl
  | cons a rest ih =>
    simp only [sumOver, List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [ih]

theorem sum_map {f : A → B} (values : List A) (g : B → Rat) :
    sumOver (values.map f) g = sumOver values (fun a => g (f a)) := by
  simp [sumOver, List.map_map, Function.comp_def]

/-- The same covariate partition is used in the selected and population
tables. T represents the assignments to Zᵀ and R the remainder. -/
structure Sources (X Y T R : Type) where
  treatments : List X
  outcomes : List Y
  external : List T
  remainder : List R
  selectedJoint : X → Y → T → R → Rat
  populationMargin : T → Rat

def Sources.selectedTreatmentCovariates (data : Sources X Y T R) (x : X) (t : T) (r : R) : Rat :=
  sumOver data.outcomes (fun y => data.selectedJoint x y t r)

def Sources.selectedCovariates (data : Sources X Y T R) (t : T) (r : R) : Rat :=
  sumOver data.treatments (fun x => data.selectedTreatmentCovariates x t r)

def Sources.selectedExternal (data : Sources X Y T R) (t : T) : Rat :=
  sumOver data.remainder (data.selectedCovariates t)

def Sources.selectedResponse (data : Sources X Y T R) (x : X) (y : Y) (t : T) (r : R) : Rat :=
  data.selectedJoint x y t r / data.selectedTreatmentCovariates x t r

def Sources.selectedRemainder (data : Sources X Y T R) (t : T) (r : R) : Rat :=
  data.selectedCovariates t r / data.selectedExternal t

def adjustment (external : List T) (remainder : List R) (response weight : T → R → Rat)
    (population : T → Rat) : Rat :=
  sumOver external fun t => sumOver remainder fun r => response t r * weight t r * population t

def Sources.recover (data : Sources X Y T R) (x : X) (y : Y) : Rat :=
  adjustment data.external data.remainder (data.selectedResponse x y)
    data.selectedRemainder data.populationMargin

def Sources.supports (data : Sources X Y T R) (x : X) : Bool :=
  data.external.all fun t =>
    decide (0 < data.selectedExternal t) &&
      data.remainder.all (fun r => decide (0 < data.selectedTreatmentCovariates x t r))

def Sources.recoverSupported (data : Sources X Y T R) (x : X) (y : Y) : Option Rat :=
  if data.supports x then some (data.recover x y) else none

theorem Sources.supports_iff (data : Sources X Y T R) (x : X) :
    data.supports x = true ↔ ∀ t ∈ data.external, 0 < data.selectedExternal t ∧
      ∀ r ∈ data.remainder, 0 < data.selectedTreatmentCovariates x t r := by
  simp [Sources.supports, List.all_eq_true]

theorem Sources.recover_supported (data : Sources X Y T R) (x : X) (y : Y)
    (support : ∀ t ∈ data.external, 0 < data.selectedExternal t ∧
      ∀ r ∈ data.remainder, 0 < data.selectedTreatmentCovariates x t r) :
    data.recoverSupported x y = some (data.recover x y) := by
  simp [Sources.recoverSupported, (data.supports_iff x).mpr support]

/-- Separate a population term that is the same across one row. -/
theorem adjustment_by_rows (external : List T) (remainder : List R)
    (response weight : T → R → Rat) (population : T → Rat) :
    adjustment external remainder response weight population =
      sumOver external (fun t => sumOver remainder (fun r => response t r * weight t r) * population t) := by
  apply sum_congr
  intro t _
  exact sum_mul_right remainder _ _

theorem selected_only_case (remainder : List R) (response weight : R → Rat) :
    adjustment [()] remainder (fun _ => response) (fun _ => weight) (fun _ => 1) =
      sumOver remainder (fun r => response r * weight r) := by
  unfold adjustment
  simp [sumOver, Rat.mul_one, Rat.add_zero]

theorem all_covariates_external_case (external : List T)
    (response population : T → Rat) :
    adjustment external [()] (fun t _ => response t) (fun _ _ => 1) population =
      sumOver external (fun t => response t * population t) := by
  unfold adjustment
  apply sum_congr
  intro t _
  simp [sumOver, Rat.mul_one, Rat.add_zero]

/-- Both quotients read the selected source. Multiplying all of its
cells by one positive constant, such as the selection rate, cancels
without changing the population margins or the formula. -/
def Sources.scaleSelected (data : Sources X Y T R) (c : Rat) : Sources X Y T R :=
  { data with selectedJoint := fun x y t r => data.selectedJoint x y t r * c }

private theorem scaled_ratio (a b c : Rat) (bNonzero : b ≠ 0) (cPositive : 0 < c) :
    (a * c) / (b * c) = a / b := by
  have cNonzero := Rat.ne_of_gt cPositive
  have bcNonzero : b * c ≠ 0 := by
    intro h
    have divide := congrArg (fun q : Rat => q * c⁻¹) h
    rw [Rat.mul_assoc, Rat.mul_comm c, Rat.inv_mul_cancel _ cNonzero, Rat.mul_one,
      Rat.zero_mul] at divide
    exact bNonzero divide
  calc
    _ = ((a / b) * (b * c)) / (b * c) := by
      rw [← Rat.mul_assoc, Rat.div_mul_cancel bNonzero]
    _ = _ := by
      rw [Rat.div_def (_ * _), Rat.mul_assoc, Rat.mul_comm (b * c),
        Rat.inv_mul_cancel _ bcNonzero, Rat.mul_one]

theorem Sources.scale_selected_preserves_recovery (data : Sources X Y T R) (x : X) (y : Y)
    (c : Rat) (cPositive : 0 < c) (support : data.supports x = true) :
    (data.scaleSelected c).recover x y = data.recover x y := by
  have treatmentRows (x : X) (t : T) (r : R) :
      (data.scaleSelected c).selectedTreatmentCovariates x t r =
        data.selectedTreatmentCovariates x t r * c :=
    sum_mul_right data.outcomes _ c
  have covariates (t : T) (r : R) :
      (data.scaleSelected c).selectedCovariates t r = data.selectedCovariates t r * c := by
    calc
      _ = sumOver data.treatments (fun x => data.selectedTreatmentCovariates x t r * c) :=
        sum_congr _ _ _ (fun x _ => treatmentRows x t r)
      _ = _ := sum_mul_right _ _ _
  have external (t : T) : (data.scaleSelected c).selectedExternal t = data.selectedExternal t * c := by
    calc
      _ = sumOver data.remainder (fun r => data.selectedCovariates t r * c) :=
        sum_congr _ _ _ (fun r _ => covariates t r)
      _ = _ := sum_mul_right _ _ _
  have supportedRows := (data.supports_iff x).mp support
  unfold Sources.recover adjustment
  apply sum_congr data.external
  intro t seen
  apply sum_congr data.remainder
  intro r row
  simp only [Sources.selectedResponse, Sources.selectedRemainder]
  rw [treatmentRows, covariates, external]
  change (data.selectedJoint x y t r * c) / (data.selectedTreatmentCovariates x t r * c) *
      ((data.selectedCovariates t r * c) / (data.selectedExternal t * c)) * data.populationMargin t = _
  rw [scaled_ratio _ _ _ (Rat.ne_of_gt ((supportedRows t seen).2 r row)) cPositive,
    scaled_ratio _ _ _ (Rat.ne_of_gt (supportedRows t seen).1) cPositive]

end

end OpenCausalScience.Papers.CorreaTianBareinboim2018.Recovery

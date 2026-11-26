module
public import OpenCausalScience.Papers.TianPearl2003.AncestralMarginal

/-! # Conditional recovery and population margins

Bareinboim, Tian and Pearl (2014), Theorems 1, 2 and 5.
Source: https://ftp.cs.ucla.edu/pub/stat_ser/r425.pdf
-/

namespace OpenCausalScience.Papers.BareinboimTianPearl2014.ConditionalRecovery

open TianPearl2003.AncestralMarginal (mass sum_masses_of_partition)

@[expose] public section

variable {Ω : Type}

def joint (massOf : (Ω → Bool) → Rat) (event condition : Ω → Bool) : Rat :=
  massOf (fun unit => event unit && condition unit)

def conditional (massOf : (Ω → Bool) → Rat) (event condition : Ω → Bool) : Rat :=
  joint massOf event condition / massOf condition

def atSelection (condition selected : Ω → Bool) : Ω → Bool :=
  fun unit => condition unit && selected unit

/-- Conditional independence, evaluated at two event values in
the indicated stratum. This is the multiplication form of
(P(event, selected \mid condition) = P(event \mid condition) P(selected \mid condition)). -/
def IndependentIn (massOf : (Ω → Bool) → Rat) (event condition selected : Ω → Bool) : Prop :=
  joint massOf event (atSelection condition selected) * massOf condition =
    joint massOf event condition * massOf (atSelection condition selected)

private theorem div_mul_cancel_right (a b : Rat) (nonzero : b ≠ 0) :
    a * b / b = a := by
  rw [Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel _ nonzero, Rat.mul_one]

private theorem ratio_eq_of_cross_mul {a b c d : Rat}
    (hb : b ≠ 0) (hd : d ≠ 0) (cross : a * d = c * b) :
    a / b = c / d := by
  have scaled : a = c / d * b := calc
    a = (a * d) / d := (div_mul_cancel_right a d hd).symm
    _ = (c * b) / d := by rw [cross]
    _ = c / d * b := by
      simp only [Rat.div_def]
      rw [Rat.mul_assoc, Rat.mul_comm b d⁻¹, ← Rat.mul_assoc]
  rw [scaled, div_mul_cancel_right _ _ hb]

/-- The input selected law normalizes the original mass on the
selection event. -/
def selectedLaw (massOf : (Ω → Bool) → Rat) (selected event : Ω → Bool) : Rat :=
  conditional massOf event selected

theorem conditional_from_selected_law (massOf : (Ω → Bool) → Rat)
    (event condition selected : Ω → Bool) (selectionSupport : massOf selected ≠ 0)
    (stratumSupport : massOf (atSelection condition selected) ≠ 0) :
    conditional (selectedLaw massOf selected) event condition =
      conditional massOf event (atSelection condition selected) := by
  have normalized : massOf (atSelection condition selected) / massOf selected ≠ 0 := by
    intro zero
    have original := Rat.div_mul_cancel (a := massOf (atSelection condition selected)) selectionSupport
    rw [zero, Rat.zero_mul] at original
    exact stratumSupport original.symm
  change
    (massOf (fun unit => (event unit && condition unit) && selected unit) / massOf selected) /
      (massOf (atSelection condition selected) / massOf selected) =
      joint massOf event (atSelection condition selected) / massOf (atSelection condition selected)
  simp only [Bool.and_assoc]
  apply ratio_eq_of_cross_mul normalized stratumSupport
  simp only [Rat.div_def]
  rw [Rat.mul_assoc, Rat.mul_comm (massOf selected)⁻¹]
  rfl

/-- The sufficiency step of Theorem 1, at any specified selection
event with nonzero stratum mass in both populations. -/
theorem selected_conditional_eq_population (massOf : (Ω → Bool) → Rat)
    (event condition selected : Ω → Bool)
    (sourceSupport : massOf (atSelection condition selected) ≠ 0)
    (targetSupport : massOf condition ≠ 0)
    (independent : IndependentIn massOf event condition selected) :
    conditional massOf event (atSelection condition selected) = conditional massOf event condition :=
  ratio_eq_of_cross_mul sourceSupport targetSupport independent

section FiniteStrata

variable {C : Type} [DecidableEq C]

def inStratum (condition : Ω → Bool) (covariates : Ω → C) (c : C) : Ω → Bool :=
  fun unit => condition unit && decide (covariates unit = c)

omit [DecidableEq C] in
private theorem sum_times (strata : List C) (factor : C → Rat) (scale : Rat) :
    (strata.map fun c => factor c * scale).sum = (strata.map factor).sum * scale := by
  induction strata with
  | nil => simp [Rat.zero_mul]
  | cons _ _ ih => simp [ih, Rat.add_mul]

/-- Theorem 2, Equation (4). The outcome conditionals are from the
selected joint and the weighting conditional is from the population.
The independence and support premises are stated for each stratum. -/
theorem recover_with_population_strata
    (atoms : List Ω) (weight : Ω → Rat) (event condition selected : Ω → Bool)
    (covariates : Ω → C) (strata : List C) (unique : strata.Nodup)
    (exhaustive : ∀ unit ∈ atoms, covariates unit ∈ strata)
    (support : ∀ c ∈ strata, mass atoms weight (inStratum condition covariates c) ≠ 0)
    (selectedSupport : ∀ c ∈ strata,
      mass atoms weight (atSelection (inStratum condition covariates c) selected) ≠ 0)
    (independent : ∀ c ∈ strata, IndependentIn (mass atoms weight) event
      (inStratum condition covariates c) selected) :
    conditional (mass atoms weight) event condition =
      (strata.map fun c => conditional (mass atoms weight) event
        (atSelection (inStratum condition covariates c) selected) *
          conditional (mass atoms weight) (fun unit => decide (covariates unit = c)) condition).sum := by
  let m := mass atoms weight
  have split : (strata.map fun c => joint m event (inStratum condition covariates c)).sum =
      joint m event condition := by
    simpa only [m, joint, inStratum, Bool.and_assoc] using
      sum_masses_of_partition strata unique atoms weight covariates exhaustive
        (fun unit => event unit && condition unit)
  calc
    conditional m event condition =
        (strata.map fun c => (joint m event (inStratum condition covariates c)) / m condition).sum := by
      rw [conditional, ← split]
      simp only [Rat.div_def, sum_times]
    _ = _ := by
      congr 1
      apply List.map_congr_left
      intro c present
      have weights : joint m (fun unit => decide (covariates unit = c)) condition =
          m (inStratum condition covariates c) := by
        unfold joint inStratum
        congr 1
        funext unit
        exact Bool.and_comm _ _
      change joint m event (inStratum condition covariates c) / m condition =
        conditional m event (atSelection (inStratum condition covariates c) selected) *
          conditional m (fun unit => decide (covariates unit = c)) condition
      have same := selected_conditional_eq_population m event (inStratum condition covariates c)
        selected (selectedSupport c present) (support c present) (independent c present)
      rw [same]
      simp only [conditional, weights, Rat.div_def]
      rw [Rat.mul_assoc (joint m event (inStratum condition covariates c)),
        ← Rat.mul_assoc (m (inStratum condition covariates c))⁻¹,
        Rat.inv_mul_cancel _ (support c present), Rat.one_mul]

/-- Theorem 5, Equation (9), given a valid population adjustment
functional and the stratum-specific selection independence. -/
theorem selection_backdoor_formula
    (massOf : (Ω → Bool) → Rat) (event treated selected : Ω → Bool)
    (covariates : Ω → C) (strata : List C) (effect : Rat)
    (adjustment : effect = (strata.map fun c =>
      conditional massOf event (inStratum treated covariates c) *
        massOf (fun unit => decide (covariates unit = c))).sum)
    (support : ∀ c ∈ strata, massOf (inStratum treated covariates c) ≠ 0)
    (selectedSupport : ∀ c ∈ strata, massOf (atSelection (inStratum treated covariates c) selected) ≠ 0)
    (independent : ∀ c ∈ strata, IndependentIn massOf event (inStratum treated covariates c) selected) :
    effect = (strata.map fun c =>
      conditional massOf event (atSelection (inStratum treated covariates c) selected) *
        massOf (fun unit => decide (covariates unit = c))).sum := by
  rw [adjustment]
  congr 1
  apply List.map_congr_left
  intro c present
  rw [selected_conditional_eq_population massOf event (inStratum treated covariates c)
    selected (selectedSupport c present) (support c present) (independent c present)]

end FiniteStrata

end
end OpenCausalScience.Papers.BareinboimTianPearl2014.ConditionalRecovery

module
public import Std

/-! # Population margin from two sources

Correa, Tian and Bareinboim (AAAI 2019), R-38, Lemma 1.
The selected table gives the conditional for the added variables; a
same-population external source gives the marginal of the original
variables. A conditional-independence identity licenses the substitution.
Source: https://causalai.net/r38.pdf#page=4
-/

namespace OpenCausalScience.Papers.CorreaTianBareinboim2019.PopulationMargin

@[expose] public section

theorem divide_mul_of_cross {a b c d : Rat} (denominator : b ≠ 0)
    (cross : a * c = d * b) : (a / b) * c = d := by
  calc
    (a / b) * c = (a * c) * b⁻¹ := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.mul_comm b⁻¹ c, ← Rat.mul_assoc]
    _ = d := by
      rw [cross, Rat.mul_assoc, Rat.mul_comm b b⁻¹, Rat.inv_mul_cancel _ denominator, Rat.mul_one]

def marginal {Base Extra : Type} (states : List Extra)
    (cell : Base → Extra → Rat) (b : Base) : Rat :=
  (states.map (cell b)).sum

/-- The fixed selected sample supplies the conditional shape. The
population margin supplies the scale of each row. -/
def recover {Base Extra : Type} (states : List Extra)
    (selected : Base → Extra → Rat) (popMargin : Base → Rat) (b : Base) (e : Extra) : Option Rat :=
  if 0 < marginal states selected b then
    some ((selected b e / marginal states selected b) * popMargin b)
  else none

theorem recover_eq_population {Base Extra : Type} (states : List Extra)
    (population selected : Base → Extra → Rat) (b : Base) (e : Extra)
    (supported : 0 < marginal states selected b)
    (selectionIndependent :
      selected b e * marginal states population b =
        population b e * marginal states selected b) :
    recover states selected (marginal states population) b e = some (population b e) := by
  simp only [recover, ite_eq_left supported, Option.some.injEq]
  exact divide_mul_of_cross (Rat.ne_of_gt supported) selectionIndependent

/-- A ratio on the selected sample is undefined at unsupported base cells. -/
theorem recover_eq_none {Base Extra : Type} (states : List Extra)
    (selected : Base → Extra → Rat) (popMargin : Base → Rat) (b : Base) (e : Extra)
    (unsupported : ¬ 0 < marginal states selected b) :
    recover states selected popMargin b e = none := by
  simp [recover, unsupported]

end
end OpenCausalScience.Papers.CorreaTianBareinboim2019.PopulationMargin

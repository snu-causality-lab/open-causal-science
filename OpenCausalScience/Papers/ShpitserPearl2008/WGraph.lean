module
public import OpenCausalScience.Papers.ShpitserPearl2008.CounterfactualDecision

/-! # A pair of binary response models for the w-graph

Shpitser and Pearl (2008), Figure 8(b) and Lemma 27. These two models
on X → Y have the same full family of single-world interventions and
positive observational cells. Their cross-world outcome coupling and a
supported conditional query differ. Each model has units on which X
changes Y.
https://www.jmlr.org/papers/volume9/shpitser08a/shpitser08a.pdf#page=24
-/

namespace OpenCausalScience.Papers.ShpitserPearl2008.WGraph

open TianPearl2003.AncestralMarginal (mass)
open CounterfactualDecision (FactorAtom baseAction conditionalMass)

@[expose] public section

/-- Each unit records natural X and the responses Y₀ and Y₁. -/
abbrev Unit := Bool × Bool × Bool

/-- Independent fair X and a response pair with fair margins. Its two
values agree with probability 3/4 in one model and 1/4 in the other. -/
def weight (second : Bool) (unit : Unit) : Rat :=
  if (unit.2.1 == unit.2.2) != second then 3 / 16 else 1 / 16

def units : List Unit := [false, true].flatMap fun x =>
  [false, true].flatMap fun low => [false, true].map fun high => (x, low, high)

def potential (unit : Unit) (setting : Bool) : Bool :=
  if setting then unit.2.2 else unit.2.1

/-- Compute the event under any combination of an X and a Y intervention. -/
def singleWorld (unit : Unit) (setX setY : Option Bool) (x y : Bool) : Bool :=
  let xValue := setX.getD unit.1
  let yValue := setY.getD (potential unit xValue)
  xValue == x && yValue == y

theorem laws_normalized : ∀ second, (units.map (weight second)).sum = 1 := by decide +kernel

theorem all_exogenous_cells_positive : ∀ second unit, 0 < weight second unit := by
  intro second unit
  rcases unit with ⟨x, low, high⟩
  cases second <;> cases x <;> cases low <;> cases high <;> decide +kernel

theorem observations_positive : ∀ second x y,
    0 < mass units (weight second) (fun unit => singleWorld unit none none x y) := by decide +kernel

theorem all_single_worlds_agree : ∀ setX setY x y,
    mass units (weight false) (fun unit => singleWorld unit setX setY x y) =
      mass units (weight true) (fun unit => singleWorld unit setX setY x y) := by
  intro setX setY x y
  cases setX with
  | none =>
    cases setY with
    | none => cases x <;> cases y <;> decide +kernel
    | some setY => cases setY <;> cases x <;> cases y <;> decide +kernel
  | some setX =>
    cases setY with
    | none => cases setX <;> cases x <;> cases y <;> decide +kernel
    | some setY => cases setX <;> cases setY <;> cases x <;> cases y <;> decide +kernel

def crossWorld (unit : Unit) : Bool := !potential unit false && potential unit true

theorem cross_world_masses :
    mass units (weight false) crossWorld = 1 / 8 ∧
      mass units (weight true) crossWorld = 3 / 8 := by decide +kernel

theorem conditional_cross_world_masses :
    conditionalMass units (weight false) (fun unit => !potential unit false)
      (fun unit => potential unit true) = some (1 / 4) ∧
    conditionalMass units (weight true) (fun unit => !potential unit false)
      (fun unit => potential unit true) = some (3 / 4) := by decide +kernel

/-- The w-graph places Y₀ and Y₁ in the same district. ID* line 8
finds that the corresponding factor sets X to both zero and one. -/
theorem conflicting_district_reports_failure :
    baseAction ([⟨1, false, fun v => if v = 0 then some false else none⟩,
      ⟨1, true, fun v => if v = 0 then some true else none⟩] : List (FactorAtom 2)) = none := by
  rfl

end
end OpenCausalScience.Papers.ShpitserPearl2008.WGraph

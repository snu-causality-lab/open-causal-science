module
public import Std

/-! # Action and observation exchange

Theorem 4.1, Rule 2, Equation (11), in Judea Pearl's AISTATS 1995
pre-proceedings.
In the model with the other actions already fixed, use the same
exogenous law in the natural and set regimes. In the set regime,
keep the natural value of Z as a separate response. Conditional
independence of that response and the set-regime outcome given the
set-regime covariates implies action/observation exchange on supported
cells. The graphical Markov implication is separate.
Source: https://proceedings.mlr.press/r0/pearl95a.html
-/

namespace OpenCausalScience.Papers.Pearl1995.RuleTwo

@[expose] public section

/-- A finite response model after fixing any other actions. The types Z, Y
and W may represent joint values. `observe` evaluates the unchanged Z
mechanism and `respond` evaluates the downstream responses when Z is set. -/
structure Model (Ω Z Y W : Type) where
  atoms : List Ω
  weight : Ω → Rat
  nonnegative : ∀ atom ∈ atoms, 0 ≤ weight atom
  normalized : (atoms.map weight).sum = 1
  observe : Ω → Z
  respond : Z → Ω → Y × W

namespace Model

variable {Ω Z Y W : Type}

def mass (model : Model Ω Z Y W) (event : Ω → Bool) : Rat :=
  (model.atoms.map fun atom => if event atom then model.weight atom else 0).sum

variable [DecidableEq Z] [DecidableEq Y] [DecidableEq W]

def observationalCovariateMass (model : Model Ω Z Y W) (z : Z) (w : W) : Rat :=
  model.mass fun atom =>
    decide (model.observe atom = z ∧ (model.respond (model.observe atom) atom).2 = w)

def observationalJointMass (model : Model Ω Z Y W) (z : Z) (y : Y) (w : W) : Rat :=
  model.mass fun atom => decide (model.observe atom = z ∧
    model.respond (model.observe atom) atom = (y, w))

def setCovariateMass (model : Model Ω Z Y W) (z : Z) (w : W) : Rat :=
  model.mass fun atom => decide ((model.respond z atom).2 = w)

def setJointMass (model : Model Ω Z Y W) (z : Z) (y : Y) (w : W) : Rat :=
  model.mass fun atom => decide (model.respond z atom = (y, w))

def setNaturalCovariateMass (model : Model Ω Z Y W) (z : Z) (w : W) : Rat :=
  model.mass fun atom => decide (model.observe atom = z ∧ (model.respond z atom).2 = w)

def setNaturalJointMass (model : Model Ω Z Y W) (z : Z) (y : Y) (w : W) : Rat :=
  model.mass fun atom => decide (model.observe atom = z ∧ model.respond z atom = (y, w))

omit [DecidableEq Y] in
theorem observational_covariate_eq_set_natural (model : Model Ω Z Y W) (z : Z) (w : W) :
    model.observationalCovariateMass z w = model.setNaturalCovariateMass z w := by
  have same : (fun atom => decide (model.observe atom = z ∧
      (model.respond (model.observe atom) atom).2 = w)) =
      (fun atom => decide (model.observe atom = z ∧ (model.respond z atom).2 = w)) := by
    funext atom
    by_cases natural : model.observe atom = z <;> simp [natural]
  exact congrArg model.mass same

theorem observational_joint_eq_set_natural (model : Model Ω Z Y W) (z : Z) (y : Y) (w : W) :
    model.observationalJointMass z y w = model.setNaturalJointMass z y w := by
  have same : (fun atom => decide (model.observe atom = z ∧
      model.respond (model.observe atom) atom = (y, w))) =
      (fun atom => decide (model.observe atom = z ∧ model.respond z atom = (y, w))) := by
    funext atom
    by_cases natural : model.observe atom = z <;> simp [natural]
  exact congrArg model.mass same

/-- The cellwise cross-product condition for independence of the set
outcome and the natural Z, given the set covariates. -/
def independentAt (model : Model Ω Z Y W) (z : Z) (y : Y) (w : W) : Prop :=
  model.setNaturalJointMass z y w * model.setCovariateMass z w =
    model.setJointMass z y w * model.setNaturalCovariateMass z w

theorem supported_action_observation_exchange (model : Model Ω Z Y W) (z : Z) (y : Y) (w : W)
    (observed : 0 < model.observationalCovariateMass z w)
    (set : 0 < model.setCovariateMass z w) (independent : model.independentAt z y w) :
    model.setJointMass z y w / model.setCovariateMass z w =
      model.observationalJointMass z y w / model.observationalCovariateMass z w := by
  unfold independentAt at independent
  rw [← model.observational_joint_eq_set_natural, ← model.observational_covariate_eq_set_natural]
    at independent
  have divided := congrArg
    (fun cell : Rat => cell / model.setCovariateMass z w / model.observationalCovariateMass z w)
    independent
  have commute : model.setJointMass z y w * model.observationalCovariateMass z w /
      model.setCovariateMass z w =
      model.setJointMass z y w / model.setCovariateMass z w *
        model.observationalCovariateMass z w := by
    simp only [Rat.div_def, Rat.mul_assoc, Rat.mul_comm (model.observationalCovariateMass z w)]
  rw [Rat.mul_div_cancel (Rat.ne_of_gt set), commute, Rat.mul_div_cancel (Rat.ne_of_gt observed)]
    at divided
  exact divided.symm

end Model

/-- Binary W → Z, W → Y, Z → Y. The two exogenous bits are an
independent fair value of W and noise with mass 1/4 on true. -/
def backDoorExample : Model (Bool × Bool) Bool Bool Bool where
  atoms := [(false, false), (false, true), (true, false), (true, true)]
  weight atom := if atom.2 then 1/8 else 3/8
  nonnegative := by intro atom _; cases atom.2 <;> decide +kernel
  normalized := by decide +kernel
  observe atom := Bool.xor atom.1 atom.2
  respond z atom := (z || atom.1, atom.1)

theorem back_door_conditioned_cells (z y w : Bool) :
    0 < backDoorExample.observationalCovariateMass z w ∧
      0 < backDoorExample.setCovariateMass z w ∧ backDoorExample.independentAt z y w := by
  unfold Model.independentAt
  cases z <;> cases y <;> cases w <;> decide +kernel

/-- Summing out W makes observational and interventional risks differ. -/
theorem back_door_unadjusted_disagrees :
    backDoorExample.mass (fun atom => (backDoorExample.respond false atom).1) = 1/2 ∧
    backDoorExample.mass (fun atom =>
      !backDoorExample.observe atom && (backDoorExample.respond (backDoorExample.observe atom) atom).1) /
      backDoorExample.mass (fun atom => !backDoorExample.observe atom) = 1/4 := by
  decide +kernel

end

end OpenCausalScience.Papers.Pearl1995.RuleTwo

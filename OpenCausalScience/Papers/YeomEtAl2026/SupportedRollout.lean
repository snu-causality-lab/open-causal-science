module
public import Std

/-!
# Yeom et al. (2026), alignment along an intervention rollout

Sections 3 and 4.4 and Appendix B.2 of the 2026-10-15 correction require
alignment at the joint parent and innovation inputs reached by a specified
intervention. This module proves pathwise equality for any finite schedule
of local mechanisms and fixed interventions, and equality of the induced
trajectory laws for finite rational innovation laws. It also proves the
neighborhood argument that extends observational almost-everywhere
alignment to observational support under continuity.

The paper's fitted CNF, noise reparameterization theorem, and continuous
conditional treatment kernels are outside the definitions in this module.

Source: https://www.sanghacklee.me/ai-corrected/TSCNF_AI_corrected_2026-10-15.pdf
-/

namespace OpenCausalScience.Papers.YeomEtAl2026.SupportedRollout

@[expose] public section

/-- Observational support expressed by positivity of every neighborhood of
the joint parent–innovation input. -/
def InSupport {I : Type} (neighborhood : I → (I → Prop) → Prop)
    (positive : (I → Prop) → Prop) (x : I) : Prop :=
  ∀ U, neighborhood x U → positive U

/-- The preimage of every neighborhood of the output is a neighborhood of
the input. The specific topology is supplied by the model. -/
def ContinuousAt {I V : Type} (inputNeighborhood : I → (I → Prop) → Prop)
    (outputNeighborhood : V → (V → Prop) → Prop) (f : I → V) (x : I) : Prop :=
  ∀ U, outputNeighborhood (f x) U → inputNeighborhood x (fun y => U (f y))

/-- Continuous mechanisms that agree observationally almost everywhere
agree on observational support. If they disagree at a supported point,
disjoint output neighborhoods and continuity give a positive-mass
observational neighborhood of disagreement. -/
theorem eq_at_supported_input {I V : Type}
    (inputNeighborhood : I → (I → Prop) → Prop)
    (outputNeighborhood : V → (V → Prop) → Prop)
    (positive : (I → Prop) → Prop)
    (monotone : ∀ {A B}, (∀ y, A y → B y) → positive A → positive B)
    (intersect : ∀ x {U V}, inputNeighborhood x U → inputNeighborhood x V →
      inputNeighborhood x (fun y => U y ∧ V y))
    (separated : ∀ a b, a ≠ b → ∃ U V,
      outputNeighborhood a U ∧ outputNeighborhood b V ∧ ∀ y, U y → V y → False)
    (reference fitted : I → V) (x : I)
    (supported : InSupport inputNeighborhood positive x)
    (reference_continuous : ContinuousAt inputNeighborhood outputNeighborhood reference x)
    (fitted_continuous : ContinuousAt inputNeighborhood outputNeighborhood fitted x)
    (almost_everywhere : ¬ positive (fun y => reference y ≠ fitted y)) :
    reference x = fitted x := by
  classical
  by_cases equal : reference x = fitted x
  · exact equal
  · exfalso
    obtain ⟨U, V, first, second, disjoint⟩ := separated _ _ equal
    have around := intersect x (reference_continuous U first) (fitted_continuous V second)
    apply almost_everywhere
    refine monotone (fun y hy equalAtY => ?_) (supported _ around)
    exact disjoint (reference y) hy.1 (equalAtY.symm ▸ hy.2)

inductive Implementation where
  | reference
  | fitted

/-- Reference and fitted equations at a local node, expressed on the same
parent–innovation input space after reparameterization. -/
structure LocalMechanism (I V : Type) where
  reference : I → V
  fitted : I → V
  aligned : I → Prop
  agrees : ∀ u, aligned u → reference u = fitted u

/-- Use the support of the joint observational law as the domain of
alignment for a nonintervened mechanism. -/
def LocalMechanism.ofContinuousSupport {I V : Type}
    (inputNeighborhood : I → (I → Prop) → Prop)
    (outputNeighborhood : V → (V → Prop) → Prop)
    (positive : (I → Prop) → Prop)
    (monotone : ∀ {A B}, (∀ y, A y → B y) → positive A → positive B)
    (intersect : ∀ x {U V}, inputNeighborhood x U → inputNeighborhood x V →
      inputNeighborhood x (fun y => U y ∧ V y))
    (separated : ∀ a b, a ≠ b → ∃ U V,
      outputNeighborhood a U ∧ outputNeighborhood b V ∧ ∀ y, U y → V y → False)
    (reference fitted : I → V)
    (reference_continuous : ∀ x, InSupport inputNeighborhood positive x →
      ContinuousAt inputNeighborhood outputNeighborhood reference x)
    (fitted_continuous : ∀ x, InSupport inputNeighborhood positive x →
      ContinuousAt inputNeighborhood outputNeighborhood fitted x)
    (almost_everywhere : ¬ positive (fun y => reference y ≠ fitted y)) : LocalMechanism I V where
  reference := reference
  fitted := fitted
  aligned := InSupport inputNeighborhood positive
  agrees x supported := eq_at_supported_input inputNeighborhood outputNeighborhood positive monotone
    intersect separated reference fitted x supported (reference_continuous x supported)
    (fitted_continuous x supported) almost_everywhere

def LocalMechanism.evaluate {I V : Type} (mechanism : LocalMechanism I V)
    (implementation : Implementation) (action : Option V) (input : I) : V :=
  match action with
  | some value => value
  | none =>
    match implementation with
    | .reference => mechanism.reference input
    | .fitted => mechanism.fitted input

def LocalMechanism.supported {I V : Type} (mechanism : LocalMechanism I V)
    (action : Option V) (input : I) : Prop :=
  match action with
  | some _ => True
  | none => mechanism.aligned input

theorem LocalMechanism.evaluate_eq {I V : Type} (mechanism : LocalMechanism I V)
    (action : Option V) (input : I) (supported : mechanism.supported action input) :
    mechanism.evaluate .reference action input = mechanism.evaluate .fitted action input := by
  cases action with
  | none => exact mechanism.agrees input supported
  | some _ => rfl

/-- A finite rollout schedule in time order, with nodes in topological
order within a time slice. The history records the earlier values needed
by subsequent stages. A stage can use a fixed intervention in place of
its local equation. The common source `Ω` can contain the initial history
and all innovations, with arbitrary dependencies. -/
inductive Schedule (Ω : Type) : Type → Type → Type 1 where
  | done {H : Type} : Schedule Ω H Unit
  | step {H I V H' Tail : Type} (mechanism : LocalMechanism I V)
      (action : Option V) (inputs : H → Ω → I) (extend : H → V → H')
      (next : Schedule Ω H' Tail) : Schedule Ω H (V × Tail)

def Schedule.rollout {Ω : Type} (implementation : Implementation) :
    {H O : Type} → Schedule Ω H O → H → Ω → O
  | _, _, .done, _, _ => ()
  | _, _, .step mechanism action inputs extend next, history, noise =>
    let value := mechanism.evaluate implementation action (inputs history noise)
    (value, next.rollout implementation (extend history value) noise)

/-- Only the input trajectory of the reference intervention is checked.
The fitted trajectory reaches the same inputs by the pathwise theorem. -/
def Schedule.referenceSupported {Ω : Type} :
    {H O : Type} → Schedule Ω H O → H → Ω → Prop
  | _, _, .done, _, _ => True
  | _, _, .step mechanism action inputs extend next, history, noise =>
    let input := inputs history noise
    mechanism.supported action input ∧
      next.referenceSupported (extend history (mechanism.evaluate .reference action input)) noise

/-- If the reference intervention visits supported inputs at all
nonintervened stages, the entire fitted trajectory equals the reference
trajectory at the same initial history and coupled noise. -/
theorem Schedule.rollout_eq {Ω H O : Type} (schedule : Schedule Ω H O) :
    ∀ history noise, schedule.referenceSupported history noise →
      schedule.rollout .reference history noise = schedule.rollout .fitted history noise := by
  induction schedule with
  | done => intro _ _ _; rfl
  | step mechanism action inputs extend next ih =>
    intro history noise supported
    obtain ⟨here, later⟩ := supported
    have head := mechanism.evaluate_eq action (inputs history noise) here
    have tail := ih _ noise later
    simp only [Schedule.rollout]
    rw [← head, tail]

/-- If coverage fails only on a null set of the coupled intervention law,
trajectory disagreement also occurs only on a null set. The probability
of events is used through monotonicity of positive mass. -/
theorem Schedule.rollout_eq_almost_everywhere {Ω H O : Type} (schedule : Schedule Ω H O)
    (initial : Ω → H) (positive : (Ω → Prop) → Prop)
    (monotone : ∀ {A B}, (∀ noise, A noise → B noise) → positive A → positive B)
    (coverage : ¬ positive (fun noise => ¬ schedule.referenceSupported (initial noise) noise)) :
    ¬ positive (fun noise =>
      schedule.rollout .reference (initial noise) noise ≠
        schedule.rollout .fitted (initial noise) noise) := by
  intro disagreement
  apply coverage
  exact monotone (fun noise different supported =>
    different (schedule.rollout_eq (initial noise) noise supported)) disagreement

/-- Every event of the trajectory also agrees up to a null set, including
events of a single outcome obtained by projecting the trajectory. -/
theorem Schedule.trajectory_event_agrees_almost_everywhere {Ω H O : Type}
    (schedule : Schedule Ω H O) (initial : Ω → H) (positive : (Ω → Prop) → Prop)
    (monotone : ∀ {A B}, (∀ noise, A noise → B noise) → positive A → positive B)
    (coverage : ¬ positive (fun noise => ¬ schedule.referenceSupported (initial noise) noise))
    (event : O → Prop) :
    ¬ positive (fun noise => ¬ (event (schedule.rollout .reference (initial noise) noise) ↔
      event (schedule.rollout .fitted (initial noise) noise))) := by
  intro differentEvent
  apply schedule.rollout_eq_almost_everywhere initial positive monotone coverage
  exact monotone (fun _ disagreement equal => disagreement (equal ▸ Iff.rfl)) differentEvent

structure FiniteInnovations (Ω : Type) where
  atoms : List Ω
  weight : Ω → Rat
  nonnegative : ∀ u ∈ atoms, 0 ≤ weight u
  normalized : (atoms.map weight).sum = 1

/-- Push the coupled finite innovation law through the rollout. -/
def Schedule.trajectoryMass {Ω H O : Type} (schedule : Schedule Ω H O)
    (implementation : Implementation) (law : FiniteInnovations Ω)
    (initial : Ω → H) (event : O → Bool) : Rat :=
  (law.atoms.map fun u =>
    if event (schedule.rollout implementation (initial u) u) then law.weight u else 0).sum

theorem Schedule.trajectory_mass_univ {Ω H O : Type} (schedule : Schedule Ω H O)
    (implementation : Implementation) (law : FiniteInnovations Ω) (initial : Ω → H) :
    schedule.trajectoryMass implementation law initial (fun _ => true) = 1 := by
  simpa [Schedule.trajectoryMass] using law.normalized

/-- The two finite trajectory distributions agree on every event when
the reference reaches aligned inputs at all positive-mass atoms. -/
theorem Schedule.trajectory_mass_eq {Ω H O : Type} (schedule : Schedule Ω H O)
    (law : FiniteInnovations Ω) (initial : Ω → H)
    (coverage : ∀ u ∈ law.atoms, 0 < law.weight u →
      schedule.referenceSupported (initial u) u) (event : O → Bool) :
    schedule.trajectoryMass .reference law initial event =
      schedule.trajectoryMass .fitted law initial event := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro u member
  by_cases zero : law.weight u = 0
  · simp [zero]
  · have positive := Rat.lt_of_le_of_ne (law.nonnegative u member) (Ne.symm zero)
    rw [schedule.rollout_eq (initial u) u (coverage u member positive)]

end

end OpenCausalScience.Papers.YeomEtAl2026.SupportedRollout

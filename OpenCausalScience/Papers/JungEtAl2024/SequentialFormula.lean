module
public import Std

/-!
# Jung, Park, and Lee (2024), finite sequential adjustment

This file follows the soundness proof of Theorem 1 in the 2026-10-25
correction (Appendix A, Lemma S.1). It derives the stage recursion by
conditional adjustment and the chain rule, and iterates the recursion over
any finite sequence of treatment, covariate, and outcome blocks.

An independent randomized assignment gives the same finite law as evaluating
the responses at that assignment. The stage proof uses exchangeability of
the potential outcome, consistency, and equality of the relevant observable
marginals under future interventions. The link from corrected SAC to these
conditions and the Gaussian necessity argument require additional graph and
causal model results.

Source: https://www.sanghacklee.me/ai-corrected/SAC_AI_corrected_2026-10-25.pdf
-/

namespace OpenCausalScience.Papers.JungEtAl2024.SequentialFormula

@[expose] public section

/-- The joint masses needed at one stage, under the law obtained by
randomizing future treatments and conditioning on their fixed values.
The treatment argument is suppressed because its value is fixed throughout.
`potentialOutcome` includes all units in the history and covariate cell,
regardless of which units naturally take the fixed treatment value. -/
structure StageMasses (H Z Y T : Type) where
  history : H → Rat
  covariate : H → Z → Rat
  treatment : H → Z → Rat
  currentOutcome : H → Z → Y → Rat
  jointOutcome : H → Z → Y → T → Rat
  potentialOutcome : H → Z → Y → T → Rat

/-- Probability of an event in a finite sample space represented by atoms
and their rational masses. -/
def eventMass {Ω : Type} (atoms : List Ω) (weight : Ω → Rat) (event : Ω → Bool) : Rat :=
  (atoms.map fun a => if event a then weight a else 0).sum

private theorem eventMass_congr {Ω : Type} (atoms : List Ω) (weight : Ω → Rat)
    {left right : Ω → Bool} (equal : ∀ a ∈ atoms, left a = right a) :
    eventMass atoms weight left = eventMass atoms weight right := by
  apply congrArg List.sum
  exact List.map_congr_left (fun a member => by rw [equal a member])

private theorem eventMass_scaled {Ω : Type} (atoms : List Ω) (weight : Ω → Rat)
    (event : Ω → Bool) (scale : Rat) :
    eventMass atoms (fun a => weight a * scale) event = eventMass atoms weight event * scale := by
  induction atoms with
  | nil => simp [eventMass]
  | cons a atoms ih =>
    change (if event a then weight a * scale else 0) +
      eventMass atoms (fun b => weight b * scale) event =
      ((if event a then weight a else 0) + eventMass atoms weight event) * scale
    rw [ih, Rat.add_mul]
    cases event a <;> simp

/-- With an independent full-support randomization of future treatments, the
slice at the specified joint assignment has atom weights multiplied by the
same positive assignment probability. Conditioning on that assignment gives
the original probability of every event evaluated at the fixed assignment.
The event may refer to factual or counterfactual responses. -/
theorem conditional_on_randomization {Ω : Type} (atoms : List Ω) (weight : Ω → Rat)
    (normalized : (atoms.map weight).sum = 1) (event : Ω → Bool)
    (assignmentProbability : Rat) (positive : 0 < assignmentProbability) :
    eventMass atoms (fun a => weight a * assignmentProbability) event /
      eventMass atoms (fun a => weight a * assignmentProbability) (fun _ => true) =
      eventMass atoms weight event := by
  rw [eventMass_scaled, eventMass_scaled]
  have total : eventMass atoms weight (fun _ => true) = 1 := by
    simpa [eventMass] using normalized
  rw [total, Rat.one_mul, Rat.mul_div_cancel (Rat.ne_of_gt positive)]

/-- Finite exogenous responses for one randomized stage, conditioned on the
chosen later treatments. `selected` indicates that the current treatment
equals its scheduled value. In the selected cell, consistency equates the
factual outcome pair with its potential outcome under the scheduled value. -/
structure StageSample (Ω H Z Y T : Type) where
  atoms : List Ω
  weight : Ω → Rat
  nonnegative : ∀ a ∈ atoms, 0 ≤ weight a
  normalized : (atoms.map weight).sum = 1
  history : Ω → H
  covariate : Ω → Z
  selected : Ω → Bool
  currentOutcome : Ω → Y
  tailOutcome : Ω → T
  potentialOutcome : Ω → Y × T
  consistency : ∀ a ∈ atoms, selected a = true →
    potentialOutcome a = (currentOutcome a, tailOutcome a)

variable {Ω H Z Y T : Type} [DecidableEq H] [DecidableEq Z] [DecidableEq Y] [DecidableEq T]

def StageSample.inCell (q : StageSample Ω H Z Y T) (h : H) (z : Z) (a : Ω) : Bool :=
  decide (q.history a = h ∧ q.covariate a = z)

def StageSample.masses (q : StageSample Ω H Z Y T) : StageMasses H Z Y T where
  history h := eventMass q.atoms q.weight (fun a => decide (q.history a = h))
  covariate h z := eventMass q.atoms q.weight (q.inCell h z)
  treatment h z := eventMass q.atoms q.weight (fun a => q.inCell h z a && q.selected a)
  currentOutcome h z y := eventMass q.atoms q.weight (fun a =>
    q.inCell h z a && q.selected a && decide (q.currentOutcome a = y))
  jointOutcome h z y t := eventMass q.atoms q.weight (fun a =>
    q.inCell h z a && q.selected a && decide ((q.currentOutcome a, q.tailOutcome a) = (y, t)))
  potentialOutcome h z y t := eventMass q.atoms q.weight (fun a =>
    q.inCell h z a && decide (q.potentialOutcome a = (y, t)))

/-- The cross-product form of conditional independence in a history and
covariate cell. The potential outcome is the pair of current and later
outcome blocks. This formulation only compares finite event probabilities. -/
def StageSample.exchangeable (q : StageSample Ω H Z Y T) (h : H) (z : Z) (y : Y) (t : T) : Prop :=
  eventMass q.atoms q.weight (fun a =>
      q.inCell h z a && q.selected a && decide (q.potentialOutcome a = (y, t))) *
    q.masses.covariate h z = q.masses.potentialOutcome h z y t * q.masses.treatment h z

omit [DecidableEq H] [DecidableEq Z] in
private theorem StageSample.selected_outcome (q : StageSample Ω H Z Y T) (keep : Ω → Bool)
    (y : Y) (t : T) :
    eventMass q.atoms q.weight (fun a =>
      keep a && q.selected a && decide (q.potentialOutcome a = (y, t))) =
    eventMass q.atoms q.weight (fun a =>
      keep a && q.selected a && decide ((q.currentOutcome a, q.tailOutcome a) = (y, t))) := by
  apply eventMass_congr
  intro a member
  cases selected : q.selected a
  · simp
  · rw [q.consistency a member selected]

/-- Consistency turns potential-outcome exchangeability into the identity
used to replace action by observation in the selected treatment cell. -/
theorem StageSample.exchangeable_cross_product (q : StageSample Ω H Z Y T)
    (h : H) (z : Z) (y : Y) (t : T) (independent : q.exchangeable h z y t) :
    q.masses.jointOutcome h z y t * q.masses.covariate h z =
      q.masses.potentialOutcome h z y t * q.masses.treatment h z := by
  unfold StageSample.exchangeable at independent
  rw [q.selected_outcome (q.inCell h z) y t] at independent
  exact independent

/-- Summing the potential-outcome masses over the current adjustment block
and conditioning on the previous history. -/
def StageMasses.interventionConditional {H Z Y T : Type} (q : StageMasses H Z Y T)
    (covariates : List Z) (h : H) (y : Y) (t : T) : Rat :=
  (covariates.map fun z => q.potentialOutcome h z y t / q.history h).sum

private theorem sum_map_add {A : Type} (values : List A) (p q : A → Rat) :
    (values.map fun a => p a + q a).sum = (values.map p).sum + (values.map q).sum := by
  have add_left_comm (a b c : Rat) : a + (b + c) = b + (a + c) := by
    rw [← Rat.add_assoc, Rat.add_comm a b, Rat.add_assoc]
  induction values with
  | nil => simp [Rat.add_zero]
  | cons a values ih =>
    simp only [List.map_cons, List.sum_cons, ih, Rat.add_assoc, add_left_comm]

private theorem sum_map_zero {A : Type} (values : List A) :
    (values.map fun _ => (0 : Rat)).sum = 0 := by
  induction values with
  | nil => rfl
  | cons a values ih => simpa [Rat.zero_add] using ih

private theorem sum_map_commute {A B : Type} (as : List A) (bs : List B) (p : A → B → Rat) :
    (as.map fun a => (bs.map fun b => p a b).sum).sum =
      (bs.map fun b => (as.map fun a => p a b).sum).sum := by
  induction as with
  | nil => exact (sum_map_zero bs).symm
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, sum_map_add, ih]

private theorem sum_selected {A : Type} [DecidableEq A] (values : List A) (key : A) (w : Rat)
    (distinct : values.Nodup) :
    (values.map fun a => if key = a then w else 0).sum = if key ∈ values then w else 0 := by
  induction values with
  | nil => simp
  | cons a values ih =>
    simp only [List.nodup_cons] at distinct
    by_cases same : key = a
    · subst key
      simp [ih distinct.2, distinct.1, Rat.add_zero]
    · simp [same, ih distinct.2, Rat.zero_add]

private theorem eventMass_divided {A : Type} (atoms : List A) (weight : A → Rat)
    (event : A → Bool) (scale : Rat) :
    eventMass atoms weight event / scale =
      (atoms.map fun a => if event a then weight a / scale else 0).sum := by
  rw [Rat.div_def, ← eventMass_scaled]
  rfl

/-- Summing distinct supported covariate cells yields the actual finite
conditional potential-outcome probability. -/
theorem StageSample.intervention_conditional_eq (q : StageSample Ω H Z Y T)
    (covariates : List Z) (h : H) (y : Y) (t : T) (distinct : covariates.Nodup)
    (complete : ∀ a ∈ q.atoms, q.history a = h → q.covariate a ∈ covariates) :
    q.masses.interventionConditional covariates h y t =
      eventMass q.atoms q.weight (fun a =>
        decide (q.history a = h ∧ q.potentialOutcome a = (y, t))) / q.masses.history h := by
  simp only [StageMasses.interventionConditional, StageSample.masses, eventMass_divided]
  rw [sum_map_commute]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a member
  by_cases present : q.history a = h ∧ q.potentialOutcome a = (y, t)
  · obtain ⟨history, outcome⟩ := present
    have inCovariates := complete a member history
    simpa [StageSample.inCell, history, outcome, inCovariates] using
      sum_selected covariates (q.covariate a) (q.weight a /
        eventMass q.atoms q.weight (fun b => decide (q.history b = h))) distinct
  · have excluded (z : Z) : ¬ (q.inCell h z a = true ∧ q.potentialOutcome a = (y, t)) := by
      intro hz
      exact present ⟨(of_decide_eq_true hz.1).1, hz.2⟩
    simp [excluded, present, sum_map_zero]

private theorem product_of_ratios (joint current treatment covariate history potential : Rat)
    (current_nonzero : current ≠ 0) (treatment_nonzero : treatment ≠ 0)
    (independent : joint * covariate = potential * treatment) :
    (covariate / history) * (current / treatment) * (joint / current) =
      potential / history := by
  have mul_left_comm (a b c : Rat) : a * (b * c) = b * (a * c) := by
    rw [← Rat.mul_assoc, Rat.mul_comm a b, Rat.mul_assoc]
  calc
    _ = (joint * covariate) * (current / current) / treatment / history := by
      simp only [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, mul_left_comm]
    _ = _ := by
      rw [independent, Rat.div_def current current, Rat.mul_inv_cancel _ current_nonzero,
        Rat.mul_one, Rat.mul_div_cancel treatment_nonzero]

/-- The finite conditional-adjustment and chain-rule calculation in the
corrected proof. Conditional independence of the potential outcome and the
current treatment is expressed by the cross-product identity after applying
consistency in the selected treatment cell. `later` is the conditional
tail-outcome probability when only the later treatments are intervened on.
The two observable conditionals use invariance under those interventions. -/
theorem StageMasses.stage_recursion {H Z Y T H' : Type} (q : StageMasses H Z Y T)
    (covariates : List Z) (extend : H → Z → Y → H')
    (observedCovariate : H → Z → Rat) (observedOutcome : H → Z → Y → Rat)
    (later : H' → T → Rat) (h : H) (y : Y) (t : T)
    (treatment_positive : ∀ z ∈ covariates, 0 < q.treatment h z)
    (outcome_positive : ∀ z ∈ covariates, 0 < q.currentOutcome h z y)
    (independent : ∀ z ∈ covariates,
      q.jointOutcome h z y t * q.covariate h z =
        q.potentialOutcome h z y t * q.treatment h z)
    (covariate_invariance : ∀ z ∈ covariates,
      observedCovariate h z = q.covariate h z / q.history h)
    (outcome_invariance : ∀ z ∈ covariates,
      observedOutcome h z y = q.currentOutcome h z y / q.treatment h z)
    (tail_conditional : ∀ z ∈ covariates,
      later (extend h z y) t = q.jointOutcome h z y t / q.currentOutcome h z y) :
    q.interventionConditional covariates h y t =
      (covariates.map fun z => observedCovariate h z * observedOutcome h z y *
        later (extend h z y) t).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro z hz
  rw [covariate_invariance z hz, outcome_invariance z hz, tail_conditional z hz]
  exact (product_of_ratios _ _ _ _ _ _ (Rat.ne_of_gt (outcome_positive z hz))
    (Rat.ne_of_gt (treatment_positive z hz)) (independent z hz)).symm

/-- History, current covariate block and outcome block may have different
state spaces at every stage. A fixed treatment value is part of the history
update and the observational outcome kernel. -/
inductive Schedule : Type → Type → Type 1 where
  | done {H : Type} : Schedule H Unit
  | step {H Z Y T H' : Type}
      (covariates : List Z) (extend : H → Z → Y → H')
      (observedCovariate : H → Z → Rat) (observedOutcome : H → Z → Y → Rat)
      (next : Schedule H' T) : Schedule H (Y × T)

/-- Nested finite sums of the chain-rule factors in Eq. (6), after fixing the
treatment values and the block of outcomes unaffected by any treatment. -/
def Schedule.adjustment : {H O : Type} → Schedule H O → H → O → Rat
  | _, _, .done, _, _ => 1
  | _, _, .step covariates extend observedCovariate observedOutcome next, h, (y, t) =>
    (covariates.map fun z => observedCovariate h z * observedOutcome h z y *
      next.adjustment (extend h z y) t).sum

/-- The sequence of conditional interventional distributions, starting with
all scheduled interventions and ending with no remaining outcomes. Each
step carries its randomized-world mass and exchangeability, invariance, and
consistency inputs, before using the stage recursion. -/
inductive StageConditions : {H O : Type} → Schedule H O → (H → O → Rat) → Prop where
  | done {H : Type} (target : H → Unit → Rat) (empty : ∀ h, target h () = 1) :
      StageConditions .done target
  | step {H Z Y T H' : Type} {covariates : List Z} {extend : H → Z → Y → H'}
      {observedCovariate : H → Z → Rat} {observedOutcome : H → Z → Y → Rat}
      {next : Schedule H' T} (target : H → Y × T → Rat) (later : H' → T → Rat)
      (q : StageMasses H Z Y T)
      (target_conditional : ∀ h y t, target h (y, t) = q.interventionConditional covariates h y t)
      (treatment_positive : ∀ h z, z ∈ covariates → 0 < q.treatment h z)
      (outcome_positive : ∀ h z y, z ∈ covariates → 0 < q.currentOutcome h z y)
      (independent : ∀ h z y t, z ∈ covariates →
        q.jointOutcome h z y t * q.covariate h z =
          q.potentialOutcome h z y t * q.treatment h z)
      (covariate_invariance : ∀ h z, z ∈ covariates →
        observedCovariate h z = q.covariate h z / q.history h)
      (outcome_invariance : ∀ h z y, z ∈ covariates →
        observedOutcome h z y = q.currentOutcome h z y / q.treatment h z)
      (tail_conditional : ∀ h z y t, z ∈ covariates →
        later (extend h z y) t = q.jointOutcome h z y t / q.currentOutcome h z y)
      (remaining : StageConditions next later) :
      StageConditions (.step covariates extend observedCovariate observedOutcome next) target

/-- Construct the stage conditions from a finite response law. The inputs
identify the head and tail responses with their respective interventional
conditionals and identify the two observable marginals in the randomized
and observational laws. -/
theorem StageConditions.step_of_sample {H' : Type} {covariates : List Z}
    {extend : H → Z → Y → H'}
    {observedCovariate : H → Z → Rat} {observedOutcome : H → Z → Y → Rat}
    {next : Schedule H' T} {target : H → Y × T → Rat} {later : H' → T → Rat}
    (q : StageSample Ω H Z Y T) (distinct : covariates.Nodup)
    (complete : ∀ a ∈ q.atoms, q.covariate a ∈ covariates)
    (target_conditional : ∀ h y t, target h (y, t) =
      eventMass q.atoms q.weight (fun a =>
        decide (q.history a = h ∧ q.potentialOutcome a = (y, t))) / q.masses.history h)
    (treatment_positive : ∀ h z, z ∈ covariates → 0 < q.masses.treatment h z)
    (outcome_positive : ∀ h z y, z ∈ covariates → 0 < q.masses.currentOutcome h z y)
    (exchangeable : ∀ h z y t, z ∈ covariates → q.exchangeable h z y t)
    (covariate_invariance : ∀ h z, z ∈ covariates →
      observedCovariate h z = q.masses.covariate h z / q.masses.history h)
    (outcome_invariance : ∀ h z y, z ∈ covariates →
      observedOutcome h z y = q.masses.currentOutcome h z y / q.masses.treatment h z)
    (tail_conditional : ∀ h z y t, z ∈ covariates →
      later (extend h z y) t = q.masses.jointOutcome h z y t / q.masses.currentOutcome h z y)
    (remaining : StageConditions next later) :
    StageConditions (.step covariates extend observedCovariate observedOutcome next) target := by
  refine .step target later q.masses ?_ treatment_positive outcome_positive ?_
    covariate_invariance outcome_invariance tail_conditional remaining
  · intro h y t
    rw [target_conditional, q.intervention_conditional_eq covariates h y t distinct]
    exact fun a member _ => complete a member
  · intro h z y t member
    exact q.exchangeable_cross_product h z y t (exchangeable h z y t member)

/-- Iterate the stage calculation for an arbitrary finite schedule. -/
theorem StageConditions.conditional_eq_adjustment {H O : Type} {schedule : Schedule H O}
    {target : H → O → Rat} (conditions : StageConditions schedule target) :
    ∀ h o, target h o = schedule.adjustment h o := by
  induction conditions with
  | done target empty =>
    intro h o
    cases o
    exact empty h
  | @step H Z Y T H' covariates extend observedCovariate observedOutcome next
      target later q target_conditional treatment_positive outcome_positive independent
      covariate_invariance outcome_invariance tail_conditional remaining ih =>
    rintro h ⟨y, t⟩
    rw [target_conditional, q.stage_recursion covariates extend observedCovariate observedOutcome
      later h y t (treatment_positive h) (fun z hz => outcome_positive h z y hz)
      (fun z hz => independent h z y t hz) (covariate_invariance h)
      (fun z hz => outcome_invariance h z y hz) (fun z hz => tail_conditional h z y t hz)]
    simp only [Schedule.adjustment, ih]

/-- The finite sequential covariate adjustment formula, including the
observational factor for the unaffected initial outcome block `Y₀`. -/
theorem sequential_adjustment_formula {Y0 O : Type} {schedule : Schedule Y0 O}
    {target : Y0 → O → Rat} (conditions : StageConditions schedule target)
    (observedInitial intervenedInitial : Y0 → Rat) (intervenedJoint : Y0 → O → Rat)
    (initial_invariance : ∀ y, intervenedInitial y = observedInitial y)
    (initial_chain_rule : ∀ y o, intervenedJoint y o = intervenedInitial y * target y o)
    (y : Y0) (o : O) :
    intervenedJoint y o = observedInitial y * schedule.adjustment y o := by
  rw [initial_chain_rule, initial_invariance, conditions.conditional_eq_adjustment]

end

end OpenCausalScience.Papers.JungEtAl2024.SequentialFormula

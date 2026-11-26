module
public import OpenCausalScience.Papers.ElahiEtAl2024.SplitNetwork

/-! The bow graph tests the intervention domain in Lemma 2 and line 8 of
Algorithm 1. The observational and intervention laws below are rational
finite laws. -/

@[expose] public section

namespace OpenCausalScience.Papers.ElahiEtAl2024.OutcomeIntervention

open SplitNetwork
open MixedGraph (Reach)

inductive Vertex
  | x | y | hidden
  deriving DecidableEq

open Vertex

/-- After cutting arrows out of the treatment in X → Y with X ↔ Y. -/
def bowArrow : Vertex → Vertex → Prop
  | .hidden, .x | .hidden, .y => True
  | _, _ => False

def intervened (onX onY : Bool) : Vertex → Prop
  | .x => onX = true
  | .y => onY = true
  | .hidden => False

def empty (_v : Vertex) : Prop :=
  False

def bowLeft (v : Vertex) : Prop := v = .x
def bowRight (v : Vertex) : Prop := v = .y

def BowCut (onX onY : Bool) : Prop :=
  IsSplitCut bowArrow bowLeft bowRight (intervened onX onY) empty

private theorem unmodified_bow_has_route :
    Reach (MoralEdge bowArrow (intervened false false) empty) x y := by
  have toHidden : MoralEdge bowArrow (intervened false false) empty x hidden := by
    exact ⟨fun h => h, fun h => h, by decide, .inr (.inl ⟨trivial, by simp [intervened]⟩)⟩
  have toOutcome : MoralEdge bowArrow (intervened false false) empty hidden y := by
    exact ⟨fun h => h, fun h => h, by decide, .inl ⟨trivial, by simp [intervened]⟩⟩
  exact .extend (.extend (.refl _) toHidden) toOutcome

private theorem cut_at_x (onY : Bool) : BowCut true onY := by
  apply (split_cut_iff_moral_cut ..).mpr
  apply moral_cut_of_arrow_partition _ _ _ _ _ (fun v => decide (v = x))
  · rintro _ rfl
    decide
  · rintro _ rfl
    decide
  · intro a b retained
    cases a <;> cases b <;> simp [remainingArrow, bowArrow, intervened] at retained ⊢

private theorem cut_at_y (onX : Bool) : BowCut onX true := by
  apply (split_cut_iff_moral_cut ..).mpr
  apply moral_cut_of_arrow_partition _ _ _ _ _ (fun v => decide (v ≠ y))
  · rintro _ rfl
    decide
  · rintro _ rfl
    decide
  · intro a b retained
    cases a <;> cases b <;> simp [remainingArrow, bowArrow, intervened] at retained ⊢

theorem bow_split_cut_iff (onX onY : Bool) :
    BowCut onX onY ↔ onX = true ∨ onY = true := by
  cases onX <;> cases onY
  · simp only [Bool.false_eq_true, or_self]
    apply iff_false_intro
    intro cut
    have moral := (split_cut_iff_moral_cut ..).mp cut
    exact moral x y rfl rfl unmodified_bow_has_route
  · simp [cut_at_y]
  · simp [cut_at_x]
  · simp [cut_at_x]

def bowCost (onX onY : Bool) : Nat :=
  (if onX then 2 else 0) + (if onY then 1 else 0)

/-- The printed costs give a unique cheapest permitted cut at the outcome copy. -/
theorem printed_cost_selects_outcome :
    BowCut false true ∧ bowCost false true = 1 ∧
    ∀ onX onY, BowCut onX onY → bowCost onX onY ≤ 1 → onX = false ∧ onY = true := by
  refine ⟨cut_at_y false, rfl, ?_⟩
  intro onX onY cut feasible
  have selected := (bow_split_cut_iff onX onY).mp cut
  cases onX <;> cases onY <;> simp [bowCost] at selected feasible ⊢

theorem protected_outcome_requires_treatment (onX : Bool) :
    BowCut onX false ↔ onX = true := by
  simpa using bow_split_cut_iff onX false

/-- A binary model with a fair hidden root and independent local sampling
of treatment and outcome conditional on their parents. -/
structure Model where
  treatmentProbability : Bool → Rat
  outcomeProbability : Bool → Bool → Rat

def cell (p : Rat) (value : Bool) : Rat := if value then p else 1 - p

def Model.observedCell (m : Model) (treatment outcome : Bool) : Rat :=
  (cell (m.treatmentProbability false) treatment * cell (m.outcomeProbability false treatment) outcome +
   cell (m.treatmentProbability true) treatment * cell (m.outcomeProbability true treatment) outcome) / 2

def Model.whenOutcomeSet (m : Model) (assigned treatment outcome : Bool) : Rat :=
  if outcome = assigned then
    (cell (m.treatmentProbability false) treatment + cell (m.treatmentProbability true) treatment) / 2
  else 0

def Model.outcomeWhenTreatmentSet (m : Model) (assigned : Bool) : Rat :=
  (m.outcomeProbability false assigned + m.outcomeProbability true assigned) / 2

def firstModel : Model where
  treatmentProbability u := if u then 3 / 4 else 1 / 4
  outcomeProbability
    | false, false => 2 / 16
    | false, true => 6 / 16
    | true, false => 10 / 16
    | true, true => 14 / 16

def secondModel : Model where
  treatmentProbability := firstModel.treatmentProbability
  outcomeProbability
    | false, false => 1 / 16
    | false, true => 3 / 16
    | true, false => 13 / 16
    | true, true => 15 / 16

def PositiveMechanisms (m : Model) : Prop :=
  (∀ u, 0 < m.treatmentProbability u ∧ m.treatmentProbability u < 1) ∧
  ∀ u x, 0 < m.outcomeProbability u x ∧ m.outcomeProbability u x < 1

theorem both_models_have_positive_mechanisms :
    PositiveMechanisms firstModel ∧ PositiveMechanisms secondModel := by
  constructor <;> constructor
  · intro u
    cases u <;> decide +kernel
  · intro u x
    cases u <;> cases x <;> decide +kernel
  · intro u
    cases u <;> decide +kernel
  · intro u x
    cases u <;> cases x <;> decide +kernel

theorem same_observations (x y : Bool) :
    firstModel.observedCell x y = secondModel.observedCell x y := by
  cases x <;> cases y <;> decide +kernel

theorem same_outcome_intervention (assigned x y : Bool) :
    firstModel.whenOutcomeSet assigned x y = secondModel.whenOutcomeSet assigned x y := rfl

theorem different_treatment_response :
    firstModel.outcomeWhenTreatmentSet true = 5 / 8 ∧
    secondModel.outcomeWhenTreatmentSet true = 9 / 16 := by
  decide +kernel

/-- The treatment is non-redundant in both models, as required by §4. -/
theorem treatment_is_nonredundant :
    firstModel.outcomeWhenTreatmentSet true ≠
      firstModel.observedCell false true + firstModel.observedCell true true ∧
    secondModel.outcomeWhenTreatmentSet true ≠
      secondModel.observedCell false true + secondModel.observedCell true true := by
  decide +kernel

/-- Setting the outcome supplies the same entire law in both models yet
leaves different treatment responses, even with the observational law. -/
theorem outcome_intervention_counterexample :
    (∀ x y, firstModel.observedCell x y = secondModel.observedCell x y) ∧
    (∀ assigned x y, firstModel.whenOutcomeSet assigned x y = secondModel.whenOutcomeSet assigned x y) ∧
    firstModel.outcomeWhenTreatmentSet true ≠ secondModel.outcomeWhenTreatmentSet true := by
  exact ⟨same_observations, same_outcome_intervention, by decide +kernel⟩

end OpenCausalScience.Papers.ElahiEtAl2024.OutcomeIntervention

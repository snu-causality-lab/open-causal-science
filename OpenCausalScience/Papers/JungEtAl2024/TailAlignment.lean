module
public import OpenCausalScience.Papers.JungEtAl2024.StageGraph

/-!
# Jung, Park, and Lee (2024), the next conditional in the corrected recursion

Lemma S.1, Eq. (A.2), in the 2026-10-25 correction conditions the later
outcomes under `do(x≥i+1)` on `Hᵢ = (Hᵢ₋₁, Zᵢ, Xᵢ, Yᵢ)`. The next
stage constructs this conditional from the history in the `do(x≥i+2)`
world and the outcomes in the `do(x≥i+1)` world. Here both worlds use the
same weighted exogenous atoms, and the next treatment is not among the
coordinates of the history or their ancestors. The history event is
therefore unchanged when releasing `Xᵢ₊₁`. An encoding that distinguishes
the scheduled history cells gives equality of the two finite event masses.
On a positive history cell the quotient is the usual conditional probability.

Source: https://www.sanghacklee.me/ai-corrected/SAC_AI_corrected_2026-10-25.pdf
-/

namespace OpenCausalScience.Papers.JungEtAl2024.TailAlignment

open OpenCausalScience
open OpenCausalScience.Papers.JungEtAl2024.SequentialFormula
open OpenCausalScience.Papers.JungEtAl2024.StageGraph
open OpenCausalScience.Papers.KwonEtAl2025.AggregateReward (Plan)

@[expose] public section

variable {n : Nat} {Source Value Noise H Z Y T H' : Type}

/-- A conditional readout of a finite weighted set of exogenous atoms. -/
def conditionalReadout {Ω A B : Type} [DecidableEq A] [DecidableEq B]
    (atoms : List Ω) (weight : Ω → Rat) (history : Ω → A) (response : Ω → B)
    (h : A) (b : B) : Rat :=
  eventMass atoms weight (fun a => decide (history a = h ∧ response a = b)) /
    eventMass atoms weight (fun a => decide (history a = h))

/-- The complete history through this stage, including the current treatment. -/
def historyTuple (s : SCMStage n Source Value Noise H Z Y T) (x : Fin n → Value) :
    H × Z × Value × Y :=
  (s.readHistory x, s.readCovariate x, x s.treatment, s.readCurrent x)

/-- The new history value in the recursion at a scheduled treatment value. -/
def extendHistory (s : SCMStage n Source Value Noise H Z Y T)
    (encode : H × Z × Value × Y → H') (h : H) (z : Z) (y : Y) : H' :=
  encode (h, z, s.value, y)

/-- The intervention target used by `SCMStage.stage_conditions`, with the
history under the future plan and the outcome pair under the joint plan. -/
def interventionTarget [DecidableEq H] [DecidableEq Y] [DecidableEq T]
    (s : SCMStage n Source Value Noise H Z Y T) : H → Y × T → Rat :=
  conditionalReadout s.atoms s.weight
    (fun a => s.readHistory (s.model.evaluate s.plan a))
    (fun a => (s.readCurrent (s.model.evaluate s.jointPlan a),
      s.readTail (s.model.evaluate s.jointPlan a)))

private theorem eventMass_congr_iff {Ω : Type} (atoms : List Ω) (weight : Ω → Rat)
    {left right : Ω → Bool} (equal : ∀ a ∈ atoms, left a = true ↔ right a = true) :
    eventMass atoms weight left = eventMass atoms weight right := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro a member
  have same := equal a member
  cases l : left a <;> cases r : right a <;> simp_all

variable [DecidableEq H] [DecidableEq Z] [DecidableEq Value] [DecidableEq Y] [DecidableEq T]
  [DecidableEq H']

/-- Releasing the next treatment leaves the history readout unchanged. The
later outcomes still use the plan that sets the next treatment. It suffices
that an encoded history cell singles out its tuple among the sampled atoms. -/
theorem tail_conditional (s : SCMStage n Source Value Noise H Z Y T)
    (encode : H × Z × Value × Y → H') {released : Plan (Fin n) Value}
    {nextTreatment : Fin n} {G : DAG n} {head : List (Fin n)}
    (compatible : ∀ p v, s.model.parent p v → G.edge p v = true)
    (otherSettings : ∀ v, v ≠ nextTreatment → s.plan v = released v)
    (nondescendant : ∀ v ∈ head, v ≠ nextTreatment ∧ ¬ G.DirectedWalk nextTreatment v)
    (historyReads : ReadsOnly head (fun x => encode (historyTuple s x)))
    (reflects : ∀ a ∈ s.atoms, ∀ h z y,
      encode (historyTuple s (s.model.evaluate s.plan a)) = extendHistory s encode h z y →
        historyTuple s (s.model.evaluate s.plan a) = (h, z, s.value, y))
    (h : H) (z : Z) (y : Y) (t : T) :
    conditionalReadout s.atoms s.weight
        (fun a => encode (historyTuple s (s.model.evaluate released a)))
        (fun a => s.readTail (s.model.evaluate s.plan a)) (extendHistory s encode h z y) t =
      s.sample.masses.jointOutcome h z y t / s.sample.masses.currentOutcome h z y := by
  have history_eq (a : Source → Noise) :
      encode (historyTuple s (s.model.evaluate s.plan a)) =
        encode (historyTuple s (s.model.evaluate released a)) := by
    apply historyReads
    intro v member
    obtain ⟨different, notBelow⟩ := nondescendant v member
    apply evaluate_eq_of_not_downstream s.model (replaced := (· ∈ [nextTreatment]))
    · intro w notReplaced
      exact otherSettings w (by simpa only [List.mem_singleton] using notReplaced)
    · exact not_downstream_of_nondescendant compatible
        (by simpa only [List.mem_singleton] using different) (by
          intro f hf
          rw [List.mem_singleton.mp hf]
          exact notBelow)
  have history_iff (a : Source → Noise) (member : a ∈ s.atoms) :
      encode (historyTuple s (s.model.evaluate released a)) = extendHistory s encode h z y ↔
        s.sample.history a = h ∧ s.sample.covariate a = z ∧
          s.model.evaluate s.plan a s.treatment = s.value ∧ s.sample.currentOutcome a = y := by
    rw [← history_eq a]
    constructor
    · intro eq
      simpa only [historyTuple, SCMStage.sample, Prod.mk.injEq] using reflects a member h z y eq
    · intro eq
      apply congrArg encode
      simpa only [historyTuple, SCMStage.sample, Prod.mk.injEq] using eq
  unfold conditionalReadout StageSample.masses StageSample.inCell
  change _ = eventMass s.atoms s.weight _ / eventMass s.atoms s.weight _
  congr 1
  · apply eventMass_congr_iff
    intro a member
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq]
    rw [history_iff a member]
    simp only [Prod.mk.injEq, and_assoc, SCMStage.sample, decide_eq_true_eq]
  · apply eventMass_congr_iff
    intro a member
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq]
    rw [history_iff a member]
    simp only [and_assoc, SCMStage.sample, decide_eq_true_eq]

/-- Adjacent stages with the same model and exogenous law give the two
representations of the rightmost conditional in Eq. (A.2). The next
stage's joint plan is the present stage's future plan. -/
theorem next_stage_target_aligned {Z' Y' T' : Type} [DecidableEq Y'] [DecidableEq T']
    (s : SCMStage n Source Value Noise H Z Y (Y' × T'))
    (next : SCMStage n Source Value Noise H' Z' Y' T')
    (encode : H × Z × Value × Y → H') {G : DAG n} {head : List (Fin n)}
    (compatible : ∀ p v, s.model.parent p v → G.edge p v = true)
    (sameModel : next.model = s.model) (sameAtoms : next.atoms = s.atoms)
    (sameWeights : next.weight = s.weight) (samePlan : next.jointPlan = s.plan)
    (sameHistory : next.readHistory = fun x => encode (historyTuple s x))
    (sameTail : (fun x => (next.readCurrent x, next.readTail x)) = s.readTail)
    (nondescendant : ∀ v ∈ head, v ≠ next.treatment ∧ ¬ G.DirectedWalk next.treatment v)
    (historyReads : ReadsOnly head next.readHistory)
    (reflects : ∀ a ∈ s.atoms, ∀ h z y,
      encode (historyTuple s (s.model.evaluate s.plan a)) = extendHistory s encode h z y →
        historyTuple s (s.model.evaluate s.plan a) = (h, z, s.value, y))
    (h : H) (z : Z) (y : Y) (t : Y' × T') :
    interventionTarget next (extendHistory s encode h z y) t =
      s.sample.masses.jointOutcome h z y t / s.sample.masses.currentOutcome h z y := by
  unfold interventionTarget
  rw [sameAtoms, sameWeights, sameModel, samePlan, sameHistory]
  change conditionalReadout s.atoms s.weight _
    (fun a => (fun x => (next.readCurrent x, next.readTail x)) (s.model.evaluate s.plan a)) _ _ = _
  rw [sameTail]
  exact tail_conditional s encode compatible (nextTreatment := next.treatment)
    (fun v different => samePlan ▸ next.jointPlan_other v different) nondescendant
    (sameHistory ▸ historyReads) reflects h z y t

/-- Construct the stage recursion with an actual next-stage target. The
history and tail equalities follow from the two plans and readouts. The
finite support and exchangeability needed for adjustment remain premises. -/
theorem stage_conditions_of_next {Z' Y' T' : Type} [DecidableEq Y'] [DecidableEq T']
    (s : SCMStage n Source Value Noise H Z Y (Y' × T'))
    (next : SCMStage n Source Value Noise H' Z' Y' T')
    (encode : H × Z × Value × Y → H') {G : DAG n} {future head : List (Fin n)}
    (compatible : ∀ p v, s.model.parent p v → G.edge p v = true)
    (planned : ∀ v, v ∉ future → s.plan v = none)
    (nondescendant : ∀ v ∈ head, v ∉ future ∧ ∀ f ∈ future, ¬ G.DirectedWalk f v)
    (treatmentInHead : s.treatment ∈ head) (nextTreatmentFuture : next.treatment ∈ future)
    (historyReads : ReadsOnly head s.readHistory)
    (covariateReads : ReadsOnly head s.readCovariate)
    (currentReads : ReadsOnly head s.readCurrent)
    (sameModel : next.model = s.model) (sameAtoms : next.atoms = s.atoms)
    (sameWeights : next.weight = s.weight) (samePlan : next.jointPlan = s.plan)
    (sameHistory : next.readHistory = fun x => encode (historyTuple s x))
    (sameTail : (fun x => (next.readCurrent x, next.readTail x)) = s.readTail)
    (reflects : ∀ a ∈ s.atoms, ∀ h z y,
      encode (historyTuple s (s.model.evaluate s.plan a)) = extendHistory s encode h z y →
        historyTuple s (s.model.evaluate s.plan a) = (h, z, s.value, y))
    {covariates : List Z} {rest : Schedule H' (Y' × T')}
    (distinct : covariates.Nodup)
    (complete : ∀ a ∈ s.sample.atoms, s.sample.covariate a ∈ covariates)
    (treatmentPositive : ∀ h z, z ∈ covariates → 0 < s.sample.masses.treatment h z)
    (outcomePositive : ∀ h z y, z ∈ covariates → 0 < s.sample.masses.currentOutcome h z y)
    (exchangeable : ∀ h z y t, z ∈ covariates → s.sample.exchangeable h z y t)
    (remaining : StageConditions rest (interventionTarget next)) :
    StageConditions (.step covariates (extendHistory s encode) s.observedCovariate
      s.observedOutcome rest) (interventionTarget s) := by
  have nextReads : ReadsOnly head next.readHistory := by
    rw [sameHistory]
    intro x x' agree
    simp only [historyTuple, historyReads x x' agree, covariateReads x x' agree,
      currentReads x x' agree, agree s.treatment treatmentInHead]
  have nextNondescendant (v : Fin n) (member : v ∈ head) :
      v ≠ next.treatment ∧ ¬ G.DirectedWalk next.treatment v := by
    obtain ⟨notFuture, notBelow⟩ := nondescendant v member
    exact ⟨fun eq => notFuture (eq ▸ nextTreatmentFuture), notBelow _ nextTreatmentFuture⟩
  refine s.stage_conditions compatible planned nondescendant treatmentInHead historyReads
    covariateReads currentReads distinct complete (fun _ _ _ => rfl) treatmentPositive
    outcomePositive exchangeable ?_ remaining
  intro h z y t _
  exact next_stage_target_aligned s next encode compatible sameModel sameAtoms sameWeights
    samePlan sameHistory sameTail nextNondescendant nextReads reflects h z y t

end

end OpenCausalScience.Papers.JungEtAl2024.TailAlignment

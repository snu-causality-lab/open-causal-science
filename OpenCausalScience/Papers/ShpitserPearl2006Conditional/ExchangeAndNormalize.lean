module
public import OpenCausalScience.Papers.Pearl1995.RuleTwo
public import OpenCausalScience.Papers.TianPearl2003.AncestralMarginal

/-! # One IDC exchange followed by conditional normalization

Shpitser and Pearl (2006), Figure 3. A Rule 2 exchange moves one
observed variable into the intervention. If the reduced joint is
available, dividing its cells by their sum over the outcome computes
the original conditional effect at supported evidence.
Source: https://ftp.cs.ucla.edu/pub/stat_ser/r329-uai.pdf#page=5
-/

namespace OpenCausalScience.Papers.ShpitserPearl2006Conditional.ExchangeAndNormalize

open Pearl1995.RuleTwo

@[expose] public section

variable {Ω Z Y W : Type} [DecidableEq Z] [DecidableEq Y] [DecidableEq W]

private theorem subevent_mass_le (weight : Ω → Rat) (atoms : List Ω)
    (nonnegative : ∀ a ∈ atoms, 0 ≤ weight a)
    (small large : Ω → Bool) (includes : ∀ a, small a = true → large a = true) :
    (atoms.map fun a => if small a then weight a else 0).sum ≤
      (atoms.map fun a => if large a then weight a else 0).sum := by
  induction atoms with
  | nil => exact Rat.le_refl
  | cons a rest ih =>
    have head : (if small a then weight a else 0) ≤ (if large a then weight a else 0) := by
      cases smallValue : small a
      · cases largeValue : large a
        · exact Rat.le_refl
        · exact nonnegative a List.mem_cons_self
      · simp [includes a smallValue]
    have tail := ih fun b member => nonnegative b (List.mem_cons_of_mem a member)
    simp only [List.map_cons, List.sum_cons]
    exact Rat.le_trans (Rat.add_le_add_right.mpr head) (Rat.add_le_add_left.mpr tail)

omit [DecidableEq Y] in
theorem action_evidence_positive_of_observational_evidence (model : Model Ω Z Y W) (z : Z) (w : W)
    (observed : 0 < model.observationalCovariateMass z w) : 0 < model.setCovariateMass z w := by
  rw [model.observational_covariate_eq_set_natural] at observed
  exact Std.lt_of_lt_of_le observed
    (subevent_mass_le model.weight model.atoms model.nonnegative
      (fun a => decide (model.observe a = z ∧ (model.respond z a).2 = w))
      (fun a => decide ((model.respond z a).2 = w))
      (fun _ h => decide_eq_true ((of_decide_eq_true h).2)))

omit [DecidableEq Z] in
theorem joint_sum_eq_evidence_mass (model : Model Ω Z Y W) (z : Z) (w : W)
    (outcomes : List Y) (unique : outcomes.Nodup)
    (exhaustive : ∀ atom ∈ model.atoms, (model.respond z atom).1 ∈ outcomes) :
    (outcomes.map fun y => model.setJointMass z y w).sum = model.setCovariateMass z w := by
  change _ = TianPearl2003.AncestralMarginal.mass model.atoms model.weight
    (fun atom => decide ((model.respond z atom).2 = w))
  rw [← TianPearl2003.AncestralMarginal.sum_masses_of_partition outcomes unique
    model.atoms model.weight (fun atom => (model.respond z atom).1) exhaustive
    (fun atom => decide ((model.respond z atom).2 = w))]
  apply congrArg List.sum
  apply List.map_congr_left
  intro y _
  apply congrArg model.mass
  funext atom
  cases model.respond z atom with
  | mk value evidence =>
    simp [Bool.and_comm]

/-- IDC line 1 is the exchange. Line 2 supplies the joint from an
unconditional identification step and normalizes the remaining outcome. -/
theorem single_exchange_then_normalize (model : Model Ω Z Y W) (z : Z) (y : Y) (w : W)
    (observed : 0 < model.observationalCovariateMass z w)
    (exchange : model.independentAt z y w)
    (outcomes : List Y) (unique : outcomes.Nodup)
    (exhaustive : ∀ atom ∈ model.atoms, (model.respond z atom).1 ∈ outcomes)
    (joint : Y → Rat) (identified : ∀ value, joint value = model.setJointMass z value w) :
    0 < (outcomes.map joint).sum ∧
      joint y / (outcomes.map joint).sum =
        model.observationalJointMass z y w / model.observationalCovariateMass z w := by
  have denominator : (outcomes.map joint).sum = model.setCovariateMass z w := by
    have pointwise : joint = fun value => model.setJointMass z value w := funext identified
    rw [pointwise]
    exact joint_sum_eq_evidence_mass model z w outcomes unique exhaustive
  have action := action_evidence_positive_of_observational_evidence model z w observed
  rw [denominator, identified y]
  exact ⟨action, model.supported_action_observation_exchange z y w observed action exchange⟩

end
end OpenCausalScience.Papers.ShpitserPearl2006Conditional.ExchangeAndNormalize

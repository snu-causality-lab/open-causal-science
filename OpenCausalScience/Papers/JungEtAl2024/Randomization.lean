module
public import OpenCausalScience.Papers.JungEtAl2024.SequentialFormula

/-!
# Jung, Park, and Lee (2024), conditioning on a randomized assignment

In the corrected Lemma S.1, the future-treatment equations in the ranked
SCM are replaced by exogenous randomizations. The realized vector of
settings and the original exogenous atom have a product law. Fixing a
setting restricts every event mass by the same multiplicative factor.
This holds for events involving both factual and potential responses
computed from the same atom. In particular, the cross-product form of
conditional independence transfers to the intervention slice. Establishing
the graph-implied counterfactual independence before taking the slice is
the separate conditional-adjustment step in the proof.

Source: https://www.sanghacklee.me/ai-corrected/SAC_AI_corrected_2026-10-25.pdf
-/

namespace OpenCausalScience.Papers.JungEtAl2024.Randomization

open OpenCausalScience.Papers.JungEtAl2024.SequentialFormula

@[expose] public section

variable {Ω A : Type} [DecidableEq A]

/-- Joint mass of a response event and a specified randomized setting.
The setting's entire joint assignment is one coordinate of the product. -/
def randomizedSliceMass (atoms : List Ω) (settings : List A) (atomWeight : Ω → Rat)
    (settingWeight : A → Rat) (scheduled : A) (event : Ω → A → Bool) : Rat :=
  eventMass (atoms.flatMap fun a => settings.map fun setting => (a, setting))
    (fun p => atomWeight p.1 * settingWeight p.2)
    (fun p => decide (scheduled = p.2) && event p.1 p.2)

/-- At a scheduled setting appearing exactly once in the setting list,
selection in the product law retains a scaled copy of the intervened event. -/
theorem randomized_slice_mass (atoms : List Ω) (settings : List A) (atomWeight : Ω → Rat)
    (settingWeight : A → Rat) (scheduled : A) (distinct : settings.Nodup)
    (present : scheduled ∈ settings) (event : Ω → A → Bool) :
    randomizedSliceMass atoms settings atomWeight settingWeight scheduled event =
      eventMass atoms atomWeight (fun a => event a scheduled) * settingWeight scheduled := by
  have row (a : Ω) :
      (settings.map fun setting =>
        if decide (scheduled = setting) && event a setting then
          atomWeight a * settingWeight setting else 0).sum =
        if scheduled ∈ settings then
          (if event a scheduled then atomWeight a * settingWeight scheduled else 0) else 0 := by
    clear present
    induction settings with
    | nil => simp
    | cons setting rest ih =>
      obtain ⟨outside, restDistinct⟩ := List.nodup_cons.mp distinct
      rw [List.map_cons, List.sum_cons, ih restDistinct]
      by_cases same : scheduled = setting
      · subst scheduled
        simp [outside, Rat.add_zero]
      · simp [same, Rat.zero_add]
  induction atoms with
  | nil => simp [randomizedSliceMass, eventMass, Rat.zero_mul]
  | cons a rest ih =>
    change (List.map _ ((settings.map fun setting => (a, setting)) ++
      (rest.flatMap fun b => settings.map fun setting => (b, setting)))).sum =
      ((if event a scheduled then atomWeight a else 0) +
        eventMass rest atomWeight (fun b => event b scheduled)) * settingWeight scheduled
    change (List.map _ (rest.flatMap fun b => settings.map fun setting => (b, setting))).sum =
      eventMass rest atomWeight (fun b => event b scheduled) * settingWeight scheduled at ih
    rw [List.map_append, List.sum_append, List.map_map, ih, Rat.add_mul]
    change (settings.map fun setting => if decide (scheduled = setting) && event a setting then
      atomWeight a * settingWeight setting else 0).sum + _ = _
    rw [row a, ite_eq_left present]
    by_cases holds : event a scheduled = true
    · rw [ite_eq_left holds, ite_eq_left holds]
    · rw [ite_eq_right holds, ite_eq_right holds, Rat.zero_mul]

/-- Conditional independence in a fixed randomized assignment transfers to
its intervention law, and conversely. The four event readouts can include
counterfactual responses, evaluated with the setting and the same atom. -/
theorem randomized_slice_cross_product_iff (atoms : List Ω) (settings : List A)
    (atomWeight : Ω → Rat) (settingWeight : A → Rat) (scheduled : A)
    (distinct : settings.Nodup) (present : scheduled ∈ settings)
    (positive : 0 < settingWeight scheduled) (both cell left right : Ω → A → Bool) :
    randomizedSliceMass atoms settings atomWeight settingWeight scheduled both *
        randomizedSliceMass atoms settings atomWeight settingWeight scheduled cell =
      randomizedSliceMass atoms settings atomWeight settingWeight scheduled left *
        randomizedSliceMass atoms settings atomWeight settingWeight scheduled right ↔
    eventMass atoms atomWeight (fun a => both a scheduled) *
        eventMass atoms atomWeight (fun a => cell a scheduled) =
      eventMass atoms atomWeight (fun a => left a scheduled) *
        eventMass atoms atomWeight (fun a => right a scheduled) := by
  simp only [randomized_slice_mass atoms settings atomWeight settingWeight scheduled distinct present]
  let scale := settingWeight scheduled
  have group (x y : Rat) : (x * scale) * (y * scale) = (x * y) * (scale * scale) := by
    rw [Rat.mul_assoc, ← Rat.mul_assoc scale y scale, Rat.mul_comm scale y,
      Rat.mul_assoc y scale scale, ← Rat.mul_assoc x y (scale * scale)]
  change (_ * scale) * (_ * scale) = (_ * scale) * (_ * scale) ↔ _
  simp only [group]
  constructor
  · intro equal
    have nonzero : scale * scale ≠ 0 := Rat.ne_of_gt (Rat.mul_pos positive positive)
    simpa only [Rat.mul_div_cancel nonzero] using congrArg (· / (scale * scale)) equal
  · intro equal
    rw [equal]

end

end OpenCausalScience.Papers.JungEtAl2024.Randomization

module
public import Std

/-! # Ancestor partition under intervention

[Hwang et al., corrected version](https://www.sanghacklee.me/ai-corrected/positivity_AI_corrected_2026-09-20.pdf),
Section 5, equation (8), and Appendix E, first step of the proof of
Proposition 5.1. The result concerns directed ancestry in a graph whose
interventions delete incoming edges. It applies to the directed part of a
semi-Markovian graph and does not use positivity or c-factor semantics.
-/

namespace OpenCausalScience.Papers.HwangEtAl2024Positivity.AncestorPartition

@[expose] public section

inductive Reaches {α : Type} (edge : α → α → Prop) : α → α → Prop where
  | refl (node : α) : Reaches edge node node
  | step {start next finish : α} : edge start next → Reaches edge next finish → Reaches edge start finish

def cutIncoming {α : Type} (edge : α → α → Prop) (targets : α → Prop) (u v : α) : Prop :=
  edge u v ∧ ¬ targets v

def ancestor {α : Type} (edge : α → α → Prop) (targets : α → Prop) (x : α) : Prop :=
  ∃ target, targets target ∧ Reaches edge x target

def outcomeAncestors {α : Type} (edge : α → α → Prop) (X Y : α → Prop) : α → Prop :=
  ancestor (cutIncoming edge X) Y

def preliminaryTreatmentAncestors {α : Type} (edge : α → α → Prop) (X Y : α → Prop) : α → Prop :=
  ancestor (cutIncoming edge Y) (fun t => X t ∧ ancestor edge Y t)

def treatmentAncestors {α : Type} (edge : α → α → Prop) (X Y : α → Prop) (x : α) : Prop :=
  preliminaryTreatmentAncestors edge X Y x ∧ ¬ outcomeAncestors edge X Y x

private theorem reaches_append {α : Type} {edge : α → α → Prop} {x y z : α}
    (prefixPath : Reaches edge x y) (suffixPath : Reaches edge y z) : Reaches edge x z := by
  induction prefixPath with
  | refl _ => exact suffixPath
  | step link _ ih => exact .step link (ih suffixPath)

private theorem reaches_uncut {α : Type} {edge : α → α → Prop} {targets : α → Prop} {x y : α}
    (path : Reaches (cutIncoming edge targets) x y) : Reaches edge x y := by
  induction path with
  | refl node => exact .refl node
  | step link _ ih => exact .step link.1 ih

private theorem path_reaches_outcome_or_treatment {α : Type} {edge : α → α → Prop}
    {X Y : α → Prop} (disjoint : ∀ node, X node → ¬ Y node)
    {x y : α} (path : Reaches edge x y) :
    Y y → outcomeAncestors edge X Y x ∨ preliminaryTreatmentAncestors edge X Y x := by
  classical
  induction path with
  | refl node =>
    intro isOutcome
    exact Or.inl ⟨node, isOutcome, .refl node⟩
  | @step start next finish link tail ih =>
    intro isOutcome
    by_cases currentOutcome : Y start
    · exact Or.inl ⟨start, currentOutcome, .refl start⟩
    by_cases nextOutcome : Y next
    · have nextNotTreatment : ¬ X next := fun treatment => disjoint next treatment nextOutcome
      exact Or.inl ⟨next, nextOutcome, .step ⟨link, nextNotTreatment⟩ (.refl next)⟩
    by_cases nextTreatment : X next
    · exact Or.inr ⟨next, ⟨nextTreatment, finish, isOutcome, tail⟩,
        .step ⟨link, nextOutcome⟩ (.refl next)⟩
    rcases ih isOutcome with ⟨target, ht, reaches⟩ | ⟨target, ht, reaches⟩
    · exact Or.inl ⟨target, ht, .step ⟨link, nextTreatment⟩ reaches⟩
    · exact Or.inr ⟨target, ht, .step ⟨link, nextOutcome⟩ reaches⟩

/-- In equation (8), the corrected `X⁺` is the complement of `Y⁺` in
`An(Y)`. The two sets are therefore a disjoint partition. -/
theorem treatment_ancestors_eq_complement {α : Type} (edge : α → α → Prop)
    (X Y : α → Prop) (disjoint : ∀ node, X node → ¬ Y node) (x : α) :
    treatmentAncestors edge X Y x ↔ ancestor edge Y x ∧ ¬ outcomeAncestors edge X Y x := by
  constructor
  · rintro ⟨⟨treatment, ⟨_, outcome, isOutcome, tail⟩, head⟩, outside⟩
    exact ⟨⟨outcome, isOutcome, reaches_append (reaches_uncut head) tail⟩, outside⟩
  · rintro ⟨⟨outcome, isOutcome, path⟩, outside⟩
    exact ⟨(path_reaches_outcome_or_treatment disjoint path isOutcome).resolve_left outside, outside⟩

theorem outcome_treatment_partition {α : Type} (edge : α → α → Prop)
    (X Y : α → Prop) (disjoint : ∀ node, X node → ¬ Y node) (x : α) :
    (outcomeAncestors edge X Y x ∨ treatmentAncestors edge X Y x) ↔ ancestor edge Y x := by
  classical
  rw [treatment_ancestors_eq_complement edge X Y disjoint x]
  constructor
  · rintro (⟨outcome, isOutcome, path⟩ | ⟨h, _⟩)
    · exact ⟨outcome, isOutcome, reaches_uncut path⟩
    · exact h
  · intro originalAncestor
    by_cases outcomeAncestor : outcomeAncestors edge X Y x
    · exact Or.inl outcomeAncestor
    · exact Or.inr ⟨originalAncestor, outcomeAncestor⟩

theorem outcome_treatment_disjoint {α : Type} (edge : α → α → Prop)
    (X Y : α → Prop) (x : α) :
    ¬ (outcomeAncestors edge X Y x ∧ treatmentAncestors edge X Y x) := by
  rintro ⟨outcomeAncestor, _, outside⟩
  exact outside outcomeAncestor

def exampleEdge (u v : Nat) : Prop :=
  (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 0 ∧ v = 2)

/-- In the graph `0 → 1 → 2`, `0 → 2`, with treatment `1` and outcome `2`,
`0` belongs to both sets if `Y⁺` is left in the preliminary treatment set. -/
theorem original_sets_can_overlap :
    outcomeAncestors exampleEdge (· = 1) (· = 2) 0 ∧
    preliminaryTreatmentAncestors exampleEdge (· = 1) (· = 2) 0 := by
  refine ⟨⟨2, rfl, .step (next := 2) ⟨Or.inr (Or.inr ⟨rfl, rfl⟩), by decide⟩ (.refl 2)⟩, ?_⟩
  exact ⟨1, ⟨rfl, 2, rfl, .step (next := 2) (Or.inr (Or.inl ⟨rfl, rfl⟩)) (.refl 2)⟩,
    .step (next := 1) ⟨Or.inl ⟨rfl, rfl⟩, by decide⟩ (.refl 1)⟩

end

end OpenCausalScience.Papers.HwangEtAl2024Positivity.AncestorPartition

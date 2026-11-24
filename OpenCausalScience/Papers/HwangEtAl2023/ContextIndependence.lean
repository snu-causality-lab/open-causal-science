module
public import Std

/-!
# Hwang et al. (2023), discrete context-set specific independence

Definition 3 and Proposition 14 of the October 2026 correction, in their
discrete setting. A positive-weight point is a supported assignment, and an
inhabited supported context represents a positive-probability discrete event.
Distribution values are represented by an arbitrary type so the equalities
apply to whole conditional laws. The continuous intersection results require
separate measure and geometry arguments.
-/

namespace OpenCausalScience.Papers.HwangEtAl2023.ContextIndependence

@[expose] public section

variable {A B Law : Type}

/-- On the supported part of a context, the output law factors through A. -/
def cssi (weight : A → B → Rat) (kernel : A → B → Law)
    (context : A → B → Prop) : Prop :=
  (∃ a b, context a b ∧ 0 < weight a b) ∧
  ∃ q : A → Law, ∀ a b, context a b → 0 < weight a b → kernel a b = q a

/-- Proposition 14(1), using the conditional law given the A coordinates. -/
theorem csi_implies_cssi (weight : A → B → Rat) (kernel : A → B → Law)
    (q : A → Law) (a : A) (positive : ∃ b, 0 < weight a b)
    (csi : ∀ b, 0 < weight a b → kernel a b = q a) :
    cssi weight kernel (fun a' _ => a' = a) := by
  obtain ⟨b, hb⟩ := positive
  refine ⟨⟨a, b, rfl, hb⟩, q, ?_⟩
  intro a' b' ha' hp
  subst a'
  exact csi b' hp

/-- Proposition 14(2), taking the common supported law within the PCI domain. -/
theorem pci_implies_cssi (weight : A → B → Rat) (kernel : A → B → Law)
    (a : A) (domain : B → Prop) (positive : ∃ b, domain b ∧ 0 < weight a b)
    (pci : ∀ b b', domain b → domain b' → 0 < weight a b → 0 < weight a b' →
      kernel a b = kernel a b') :
    cssi weight kernel (fun a' b => a' = a ∧ domain b) := by
  obtain ⟨reference, hd, hw⟩ := positive
  refine ⟨⟨a, reference, ⟨rfl, hd⟩, hw⟩, fun _ => kernel a reference, ?_⟩
  rintro a' b ⟨ha', hd'⟩ hw'
  subst a'
  exact pci b reference hd' hd hw' hw

/-- In the support formulation, changing a kernel at zero-weight points does
not change its CSSI. -/
theorem cssi_congr_on_support {weight : A → B → Rat} {kernel other : A → B → Law}
    {context : A → B → Prop}
    (same : ∀ a b, context a b → 0 < weight a b → kernel a b = other a b) :
    cssi weight kernel context ↔ cssi weight other context := by
  constructor
  · rintro ⟨positive, q, h⟩
    exact ⟨positive, q, fun a b hc hp => (same a b hc hp).symm.trans (h a b hc hp)⟩
  · rintro ⟨positive, q, h⟩
    exact ⟨positive, q, fun a b hc hp => (same a b hc hp).trans (h a b hc hp)⟩

/-- A pointwise factorization can fail even when all supported laws agree. -/
theorem zero_mass_changed_law :
    cssi (fun (_ : Unit) (b : Bool) => if b then 0 else 1) (fun _ b => b)
      (fun _ _ => True) ∧
    ¬ ∃ q : Unit → Bool, ∀ b, b = q () := by
  constructor
  · refine ⟨⟨(), false, trivial, by decide⟩, fun _ => false, ?_⟩
    intro _ b _ hp
    cases b
    · rfl
    · exact False.elim ((by decide : ¬ (0 : Rat) < 0) hp)
  · rintro ⟨q, equal⟩
    exact Bool.false_ne_true ((equal false).trans (equal true).symm)

end

end OpenCausalScience.Papers.HwangEtAl2023.ContextIndependence

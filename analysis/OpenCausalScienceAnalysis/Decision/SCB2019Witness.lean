import MecLean.Scb2018.Thm6

/-!
# A pairwise-root POMIS witness

For the revised Proposition 3 of Lee and Bareinboim (2019), choose a model
on the projected diagram in which each independent root enters at most two
equations. The explicit Lee–Bareinboim (2018) witness has this property.
It makes the given POMIS strictly better than every competing DMIS in the
same model.

Source: https://www.sanghacklee.me/ai-corrected/SCB2019_AI_corrected_2026-09-19.pdf
-/

namespace OpenCausalScienceAnalysis.Scb2019

open Mec Mec.ScbMec

variable {n : ℕ}

/-- Every independent exogenous root is used by at most two declared equations. -/
def PairwiseRoots (m : Model n) : Prop :=
  ∀ l : m.L, (Finset.univ.filter (fun v => l ∈ m.scm.toMech.ex v)).card ≤ 2

/-- A private root has one endpoint and an edge root has at most two. -/
theorem card_le_two_of_rootScope {G : ADMG n} {l : Roots n} {readers : Finset (Fin n)}
    (scope : ∀ v ∈ readers, l ∈ rootScope G v) : readers.card ≤ 2 := by
  cases l with
  | inl a =>
    refine (Finset.card_le_card (t := ({a} : Finset (Fin n))) ?_).trans (by simp)
    intro v hv
    rcases mem_rootScope.mp (scope v hv) with h | ⟨b, c, h, _, _⟩
    · exact Finset.mem_singleton.mpr (Sum.inl_injective h).symm
    · cases h
  | inr ends =>
    obtain ⟨a, b⟩ := ends
    refine (Finset.card_le_card (t := ({a, b} : Finset (Fin n))) ?_).trans Finset.card_le_two
    intro v hv
    rcases mem_rootScope.mp (scope v hv) with h | ⟨a', b', h, _, hend⟩
    · cases h
    · have eq : (a, b) = (a', b') := Sum.inr_injective h
      cases eq
      rcases hend with ha | hb
      · exact Finset.mem_insert.mpr (Or.inl ha.symm)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hb.symm))

private theorem wmodel_pairwise {G : ADMG n} (hG : G.WF) (T : Finset (Fin n))
    (K : ℕ) [NeZero K] : PairwiseRoots (LB18.wmodel G hG T K) := by
  intro l
  apply card_le_two_of_rootScope (G := G) (l := l)
  intro v hv
  simp only [Finset.mem_filter] at hv
  exact hv.2

/-- For every POMIS, one compatible finite SCM with pairwise roots preserves the
strict comparison with all other DMISs in the diagram. -/
theorem exists_pairwise_pomis_witness {G : ADMG n} (hG : G.WF)
    {y : Fin n} {X : Finset (Fin n)} (hX : POMIS (ConfDiag G) y X) :
    ∃ (m : Model n) (r : m.X y → ℝ), ConfDiag G m ∧ PairwiseRoots m ∧
      ∀ W, DMIS (ConfDiag G) y W → W ≠ X → m.best y r W < m.best y r X := by
  obtain ⟨T, hT, hB⟩ := Scb2018.thm6_onlyif hG hX
  obtain ⟨K, nonzero, hbest⟩ := LB18.exists_pomis_witness hG hT hB
  let : NeZero K := nonzero
  exact ⟨LB18.wmodel G hG T K, LB18.reward G hG T X K y, LB18.wconf hG T K,
    wmodel_pairwise hG T K, hbest⟩

end OpenCausalScienceAnalysis.Scb2019

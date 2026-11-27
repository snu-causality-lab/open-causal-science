import OpenCausalScienceAnalysis.Decision.SCB2019Restoration

/-!
# Lee and Bareinboim (2019), corrected Proposition 3

Every projected POMIS has a witness on the original diagram for all comparisons
with feasible minimal intervention sets. Choose a pairwise-root witness on the
projected diagram, then undo the eliminations in reverse order. The retained
variables keep their domains, and a restored variable may take tuple values.

Source: https://www.sanghacklee.me/ai-corrected/SCB2019_AI_corrected_2026-09-19.pdf
-/

namespace OpenCausalScienceAnalysis.Scb2019

open Mec Mec.ScbMec

variable {n : ℕ}

/-- Undo the projections, preserving every best reward for a retained intervention set. -/
theorem restore_projected_witness {G : ADMG n} (hG : G.WF) (removed : List (Fin n))
    {y : Fin n} (hy : y ∉ removed) (m : Model n) (r : m.X y → ℝ)
    (hm : ConfDiag (project G removed) m) (pairs : PairwiseRoots m) :
    ∃ (original : Model n) (reward : original.X y → ℝ),
      ConfDiag G original ∧ PairwiseRoots original ∧
      ∀ S, (∀ w ∈ removed, w ∉ S) → original.best y reward S = m.best y r S := by
  induction removed generalizing G with
  | nil =>
    exact ⟨m, r, hm, pairs, fun _ _ => rfl⟩
  | cons w rest ih =>
    have hw : y ≠ w := fun eq => hy (List.mem_cons.mpr (Or.inl eq))
    have hrest : y ∉ rest := fun h => hy (List.mem_cons_of_mem w h)
    obtain ⟨beforeRest, rewardBeforeRest, hmodel, hpair, hbest⟩ :=
      ih (eliminate_wf hG w) hrest hm
    obtain ⟨original, reward, horiginal, hpairs, preserved⟩ :=
      restore_eliminated hG w beforeRest hmodel hpair y hw rewardBeforeRest
    refine ⟨original, reward, horiginal, hpairs, fun S avoids => ?_⟩
    exact (preserved S (avoids w List.mem_cons_self)).trans
      (hbest S (fun v hv => avoids v (List.mem_cons_of_mem w hv)))

/-- Corrected Proposition 3 on finite SCMs with freely chosen state spaces. One SCM makes
the projected POMIS strictly better than every other feasible MIS of the original graph. -/
theorem preserves_pomis_witnesses {G : ADMG n} (hG : G.WF) (removed : List (Fin n))
    {y : Fin n} (hy : y ∉ removed) {X : Finset (Fin n)}
    (optimal : POMIS (ConfDiag (project G removed)) y X) :
    ∃ (original : Model n) (reward : original.X y → ℝ), ConfDiag G original ∧
      ∀ S, MIS (ConfDiag G) y S → (∀ w ∈ removed, w ∉ S) → S ≠ X →
        original.best y reward S < original.best y reward X := by
  obtain ⟨m, r, hm, pairs, strict⟩ :=
    exists_pairwise_pomis_witness (project_wf hG removed) optimal
  obtain ⟨original, reward, compatible, _, preserved⟩ :=
    restore_projected_witness hG removed hy m r hm pairs
  have hX := projected_dmis_avoids_removed hG removed hy optimal.1
  refine ⟨original, reward, compatible, fun S minimal feasible distinct => ?_⟩
  have projected := (projected_dmis_iff hG removed hy feasible).mpr
    (dmis_of_mis_diag hG minimal)
  rw [preserved S feasible, preserved X hX]
  exact strict S projected distinct

end OpenCausalScienceAnalysis.Scb2019

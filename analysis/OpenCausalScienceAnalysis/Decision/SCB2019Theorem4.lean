import OpenCausalScienceAnalysis.Decision.SCB2019ForwardProjection
import OpenCausalScienceAnalysis.Decision.SCB2019Proposition3

/-!
# Lee and Bareinboim (2019), Theorem 4

The POMISs of a causal diagram with non-manipulable vertices are the POMISs
of its projection. Forward projection transports universal border dominance
to the original diagram. Corrected Proposition 3 supplies the converse.

Source: https://www.sanghacklee.me/ai-corrected/SCB2019_AI_corrected_2026-09-19.pdf
-/

namespace OpenCausalScienceAnalysis.Scb2019

open Mec Mec.ScbMec Mec.Scb2018

variable {n : ℕ}

/-- A feasible MIS that strictly beats every other feasible MIS in one compatible SCM. -/
def ConstrainedPOMIS (G : ADMG n) (removed : List (Fin n)) (y : Fin n)
    (X : Finset (Fin n)) : Prop :=
  (∀ w ∈ removed, w ∉ X) ∧ MIS (ConfDiag G) y X ∧
    ∃ (m : Model n) (r : m.X y → ℝ), ConfDiag G m ∧
      ∀ Z, MIS (ConfDiag G) y Z → (∀ w ∈ removed, w ∉ Z) → Z ≠ X →
        m.best y r Z < m.best y r X

/-- The border of a territory in the projected graph weakly dominates the original
intervention set in every compatible original model. -/
theorem best_le_projected_border {G : ADMG n} (hG : G.WF) (removed : List (Fin n))
    {y : Fin n} (hy : y ∉ removed) {X T : Finset (Fin n)}
    (allowed : ∀ w ∈ removed, w ∉ X) (territory : DiagUCT (project G removed) y X T)
    (m : Model n) (hm : ConfDiag G m) (r : m.X y → ℝ) :
    m.best y r X ≤ m.best y r (diagBorder (project G removed) T) := by
  have border := dmis_diagBorder (project_wf hG removed) territory
  have borderAllowed := projected_dmis_avoids_removed hG removed hy border
  obtain ⟨projected, reward, conforms, preserved⟩ :=
    project_model_preserves_best removed m hm hy r
  rw [← preserved X allowed, ← preserved _ borderAllowed]
  exact best_le_best_diagBorder territory projected conforms reward

theorem constrained_pomis_iff_projected_pomis {G : ADMG n} (hG : G.WF)
    (removed : List (Fin n)) {y : Fin n} (hy : y ∉ removed) (X : Finset (Fin n)) :
    ConstrainedPOMIS G removed y X ↔ POMIS (ConfDiag (project G removed)) y X := by
  have hH := project_wf hG removed
  constructor
  · rintro ⟨allowed, minimal, m, reward, compatible, strict⟩
    have outcome : y ∈ diagH (project G removed) y X :=
      mem_diagH.mpr ⟨minimal.1, Reach.refl y⟩
    obtain ⟨T, _, territory⟩ := exists_diagMUCT (diagUCT_whole outcome)
    have eq : diagBorder (project G removed) T = X := by
      by_contra distinct
      have border := dmis_diagBorder hH territory.1
      have borderAllowed := projected_dmis_avoids_removed hG removed hy border
      have borderMinimal := dmis_mis ((projected_dmis_iff hG removed hy borderAllowed).mp border)
      exact (not_lt_of_ge (best_le_projected_border hG removed hy allowed territory.1
        m compatible reward)) (strict _ borderMinimal borderAllowed distinct)
    exact thm6_if hH territory eq
  · intro projected
    have allowed := projected_dmis_avoids_removed hG removed hy projected.1
    exact ⟨allowed, dmis_mis ((projected_dmis_iff hG removed hy allowed).mp projected.1),
      preserves_pomis_witnesses hG removed hy projected⟩

/-- Theorem 4 for finite SCMs with freely chosen domains and unused permitted inputs. -/
theorem constrained_pomis_eq_projected_pomis {G : ADMG n} (hG : G.WF)
    (removed : List (Fin n)) {y : Fin n} (hy : y ∉ removed) :
    {X : Finset (Fin n) | ConstrainedPOMIS G removed y X} =
      {X : Finset (Fin n) | POMIS (ConfDiag (project G removed)) y X} :=
  Set.ext (constrained_pomis_iff_projected_pomis hG removed hy)

end OpenCausalScienceAnalysis.Scb2019

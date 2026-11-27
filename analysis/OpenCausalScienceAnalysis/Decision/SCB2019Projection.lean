import MecLean.ScbMec.MIS

/-!
# Projection of non-manipulable vertices

Eliminating one vertex substitutes its equation into each child's equation. Directed
edges contract through the eliminated vertex. Bidirected edges record an old shared
source, a shared source passed on by substitution, or the eliminated common parent.
The eliminated vertex is isolated to keep the same finite vertex type throughout.

Source: https://www.sanghacklee.me/ai-corrected/SCB2019_AI_corrected_2026-09-19.pdf
-/

namespace OpenCausalScienceAnalysis.Scb2019

open Finset Mec Mec.ScbMec

variable {n : ℕ}

/-- Latent projection through one vertex, keeping its index isolated. -/
def eliminate (G : ADMG n) (w : Fin n) : ADMG n where
  dir a b := decide (a ≠ w ∧ b ≠ w) && (G.dir a b || (G.dir a w && G.dir w b))
  bi a b := decide (a ≠ w ∧ b ≠ w ∧ a ≠ b) &&
    (G.bi a b || (G.bi a w && G.dir w b) || (G.bi b w && G.dir w a) ||
      (G.dir w a && G.dir w b))

theorem dir_eliminate_iff (G : ADMG n) (w a b : Fin n) :
    (eliminate G w).dir a b = true ↔
      a ≠ w ∧ b ≠ w ∧ (G.dir a b = true ∨ (G.dir a w = true ∧ G.dir w b = true)) := by
  simp [eliminate, and_assoc]

theorem bi_eliminate_iff (G : ADMG n) (w a b : Fin n) :
    (eliminate G w).bi a b = true ↔ a ≠ w ∧ b ≠ w ∧ a ≠ b ∧
      (G.bi a b = true ∨ (G.bi a w = true ∧ G.dir w b = true) ∨
        (G.bi b w = true ∧ G.dir w a = true) ∨ (G.dir w a = true ∧ G.dir w b = true)) := by
  simp [eliminate, and_assoc]
  tauto

private theorem expand_reach {G : ADMG n} {w a b : Fin n} {S : Finset (Fin n)}
    (hw : w ∉ S) (path : Reach (eliminate G w).dir S a b) : Reach G.dir S a b := by
  induction path with
  | refl => exact Reach.refl _
  | @tail c d _ edge ih =>
    rcases (dir_eliminate_iff G w c d).mp edge.1 with ⟨_, _, direct | ⟨into, out⟩⟩
    · exact Reach.tail ih direct edge.2
    · exact Reach.tail (Reach.tail ih into hw) out edge.2

theorem eliminate_wf {G : ADMG n} (hG : G.WF) (w : Fin n) : (eliminate G w).WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    apply Bool.eq_false_iff.mpr
    rintro h
    rcases (dir_eliminate_iff G w a a).mp h with ⟨_, _, direct | ⟨into, out⟩⟩
    · simp [hG.1 a] at direct
    · exact hG.2.2.2 a w into (Reach.single out (by simp))
  · intro a
    simp [eliminate]
  · intro a b
    apply Bool.eq_iff_iff.mpr
    rw [bi_eliminate_iff, bi_eliminate_iff, hG.2.2.1 a b]
    have distinct : a ≠ b ↔ b ≠ a := ne_comm
    tauto
  · intro a b edge cycle
    have back : Reach G.dir ∅ b a := expand_reach (by simp) cycle
    rcases (dir_eliminate_iff G w a b).mp edge with ⟨_, _, direct | ⟨into, out⟩⟩
    · exact hG.2.2.2 a b direct back
    · exact hG.2.2.2 a w into (Reach.head out (by simp) back)

private theorem contract_reach {G : ADMG n} (hG : G.WF) {w a b : Fin n}
    {S : Finset (Fin n)} (ha : a ≠ w) (path : Reach G.dir S a b) :
    (b ≠ w → Reach (eliminate G w).dir S a b) ∧
      (b = w → ∃ c ≠ w, Reach (eliminate G w).dir S a c ∧ G.dir c w = true) := by
  induction path with
  | refl => exact ⟨fun _ => Reach.refl _, fun eq => (ha eq).elim⟩
  | @tail c d _ step ih =>
    by_cases hc : c = w
    · subst c
      have hd : d ≠ w := by
        intro eq
        have loop : G.dir w w = true := eq ▸ step.1
        simp [hG.1 w] at loop
      obtain ⟨p, hp, path, edge⟩ := ih.2 rfl
      refine ⟨fun _ => ?_, fun eq => (hd eq).elim⟩
      exact Reach.tail path ((dir_eliminate_iff G w p d).mpr
        ⟨hp, hd, Or.inr ⟨edge, step.1⟩⟩) step.2
    · constructor
      · intro hd
        exact Reach.tail (ih.1 hc) ((dir_eliminate_iff G w c d).mpr
          ⟨hc, hd, Or.inl step.1⟩) step.2
      · rintro rfl
        exact ⟨c, hc, ih.1 hc, step.1⟩

/-- A path between retained vertices can be contracted or expanded without visiting
another intervention vertex. -/
theorem eliminate_ancAvoid_iff {G : ADMG n} (hG : G.WF) {w a b : Fin n}
    {S : Finset (Fin n)} (hw : w ∉ S) (ha : a ≠ w) (hb : b ≠ w) :
    (eliminate G w).AncAvoid S a b ↔ G.AncAvoid S a b :=
  ⟨expand_reach hw, fun h => (contract_reach hG ha h).1 hb⟩

/-- Apply the one-vertex projections in the supplied order. -/
def project (G : ADMG n) (removed : List (Fin n)) : ADMG n :=
  removed.foldl eliminate G

theorem project_wf {G : ADMG n} (hG : G.WF) (removed : List (Fin n)) :
    (project G removed).WF := by
  induction removed generalizing G with
  | nil => exact hG
  | cons w rest ih => exact ih (eliminate_wf hG w)

theorem project_ancAvoid_iff {G : ADMG n} (hG : G.WF) (removed : List (Fin n))
    {S : Finset (Fin n)} {a b : Fin n} (hs : ∀ v ∈ removed, v ∉ S)
    (ha : a ∉ removed) (hb : b ∉ removed) :
    (project G removed).AncAvoid S a b ↔ G.AncAvoid S a b := by
  induction removed generalizing G with
  | nil => rfl
  | cons w rest ih =>
    simp only [List.mem_cons, not_or] at ha hb
    exact (ih (eliminate_wf hG w) (fun v hv => hs v (List.mem_cons_of_mem w hv)) ha.2 hb.2).trans
      (eliminate_ancAvoid_iff hG (hs w List.mem_cons_self) ha.1 hb.1)

private theorem project_no_outgoing (G : ADMG n) (removed : List (Fin n)) {a : Fin n}
    (ha : a ∈ removed ∨ ∀ b, G.dir a b = false) (b : Fin n) :
    (project G removed).dir a b = false := by
  induction removed generalizing G with
  | nil => exact (ha.resolve_left (by simp)) b
  | cons w rest ih =>
    apply ih
    rcases ha with h | absent
    · rcases List.mem_cons.mp h with rfl | inRest
      · right
        intro c
        simp [eliminate]
      · exact Or.inl inRest
    · right
      intro c
      simp [eliminate, absent]

theorem projected_dmis_avoids_removed {G : ADMG n} (hG : G.WF) (removed : List (Fin n))
    {y : Fin n} {S : Finset (Fin n)} (hy : y ∉ removed)
    (hS : DMIS (ConfDiag (project G removed)) y S) : ∀ w ∈ removed, w ∉ S := by
  intro w hw hws
  have crit := (mis_diag_iff (project_wf hG removed) hS.1).mp (dmis_mis hS)
  have path := crit w hws
  rcases Relation.ReflTransGen.cases_head path with eq | ⟨c, step, _⟩
  · exact hy (eq ▸ hw)
  · simp [project_no_outgoing G removed (Or.inl hw) c] at step

/-- The feasible minimal intervention sets in the original and projected graphs coincide. -/
theorem projected_dmis_iff {G : ADMG n} (hG : G.WF) (removed : List (Fin n))
    {y : Fin n} {S : Finset (Fin n)} (hy : y ∉ removed) (hs : ∀ w ∈ removed, w ∉ S) :
    DMIS (ConfDiag (project G removed)) y S ↔ DMIS (ConfDiag G) y S := by
  have same : AncCrit (project G removed) y S ↔ AncCrit G y S := by
    constructor <;> intro crit a ha
    · exact (project_ancAvoid_iff hG removed hs (fun hw => hs a hw ha) hy).mp (crit a ha)
    · exact (project_ancAvoid_iff hG removed hs (fun hw => hs a hw ha) hy).mpr (crit a ha)
  constructor
  · intro h
    exact dmis_diag_of_ancCrit hG h.1
      (same.mp ((mis_diag_iff (project_wf hG removed) h.1).mp (dmis_mis h)))
  · intro h
    exact dmis_diag_of_ancCrit (project_wf hG removed) h.1
      (same.mpr ((mis_diag_iff hG h.1).mp (dmis_mis h)))

end OpenCausalScienceAnalysis.Scb2019

import MecLean.CtfScb.Witness

set_option linter.unusedSectionVars false

/-!
# Possibly optimal counterfactual specifications

The characterization uses the interventional border of the reward-ancestral subgraph after
deleting the fixed input edges. Enumeration returns pruned representatives. Without
confounding between the reward and its ancestors, the ordinary intervention on its
parents is the unique class up to equivalence.
-/

open Finset

namespace Mec.CtfScb

open Mec Mec.ScbMec Mec.Scb2018

variable {n : ℕ}

/-- **`thm: ctf-pomis`**: a parent-input specification is a
ctf-POMIS with respect to `⟨𝒢, Y⟩` iff `IB(𝓗_{𝐗_{∗∗}}, Y) = ∅`, with
`𝓗_{𝐗_{∗∗}} = 𝒢_{𝐗_{∗∗}}[An(Y)_{𝒢_{𝐗_{∗∗}}}]`.  The ICLR's Thm. 2, with the
regime graph of, is false (`ICLR.C1`). -/
theorem ctfPomis_iff {G : ADMG n} (hG : G.WF) {y : Fin n} {F : EdgeSet n} :
    CtfPOMIS G y F ↔ ctfIB G y F = ∅ :=
  ⟨ctfPomis_onlyif hG, ctfPomis_if hG⟩

/-- **`thm: enumerating ctf-pomis`**: `alg: ctf-pomis` returns exactly the
ctf-POMISs with respect to `⟨𝒢, Y⟩`: every returned specification is a ctf-POMIS, and every
ctf-POMIS is returned up to equivalence (its pruned specification is returned). -/
theorem enumerating_ctfPOMIS {G : ADMG n} (hG : G.WF) {y : Fin n} :
    (∀ F ∈ ctfPOMISs G y, CtfPOMIS G y F) ∧
      ∀ F, CtfPOMIS G y F → relevant G y F ∈ ctfPOMISs G y := by
  refine ⟨fun F hF => (ctfPomis_iff hG).mpr (mem_ctfPOMISs_iff.mp hF).2.2, fun F hF => ?_⟩
  rw [mem_ctfPOMISs_iff]
  refine ⟨relevant_relevant G y F, relevant_subset_hEdges G y F, ?_⟩
  rw [ctfIB_relevant]
  exact (ctfPomis_iff hG).mp hF

/-! Auxiliary lemmas of this file are in the namespace `Mec.CtfScb.POMISAux`. -/

namespace POMISAux

variable {G : ADMG n} {y : Fin n}

/-- `𝒢_F` is acyclic when `𝒢` is. -/
theorem wf_cutE (hG : G.WF) (F : EdgeSet n) : (G.cutE F).WF := by
  refine ⟨fun i => ?_, fun i => hG.bi_irrefl i, fun i j => hG.bi_symm i j,
    fun i j hij hji => ?_⟩
  · simp [ADMG.cutE, hG.dir_irrefl i]
  · exact hG.acyclic (ADMG.cutE_dir.mp hij).1
      (Reach.mono_rel (R := (G.cutE F).dir) (R' := G.dir)
        (fun a b _ hab => (ADMG.cutE_dir.mp hab).1) hji)

theorem mem_inEdges {p v : Fin n} : (p, v) ∈ inEdges G y ↔ G.dir p v = true ∧ v = y := by
  simp only [inEdges, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_paSet {v : Fin n} : v ∈ paSet G y ↔ G.dir v y = true := by
  simp only [paSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- When every input of `f_Y` is selected, only `Y` reaches `Y` in `𝒢_F`. -/
theorem diagH_eq_singleton {F : EdgeSet n} (h : ∀ v, G.dir v y = true → (v, y) ∈ F) :
    diagH (G.cutE F) y ∅ = {y} := by
  ext v
  rw [BorderAux.mem_diagH_empty, Finset.mem_singleton]
  constructor
  · intro hv
    rcases Relation.ReflTransGen.cases_tail hv with e | ⟨c, _, hcy⟩
    · exact e.symm
    · exact absurd (h c (ADMG.cutE_dir.mp hcy.1).1) (ADMG.cutE_dir.mp hcy.1).2
  · intro hv
    rw [hv]
    exact Reach.refl y

end POMISAux

section Unconfounded

variable {G : ADMG n} {y : Fin n}

/-- The ordinary intervention on `Pa(Y)_𝒢`, as a specification, prunes to the inputs of `f_Y`. -/
theorem relevant_outE_paSet (hG : G.WF) : relevant G y (G.outE (paSet G y)) = inEdges G y := by
  have hall : ∀ v, G.dir v y = true → (v, y) ∈ G.outE (paSet G y) := fun v hv =>
    ADMG.mem_outE.mpr ⟨POMISAux.mem_paSet.mpr hv, hv⟩
  have hH := POMISAux.diagH_eq_singleton hall
  ext ⟨p, v⟩
  rw [BorderAux.mem_relevant, hH, Finset.mem_singleton, POMISAux.mem_inEdges, ADMG.mem_outE]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, h1⟩, h1, h2⟩
    show p ∈ paSet G y
    rw [POMISAux.mem_paSet, ← h2]
    exact h1

/-- The specification `inEdges G y`, with a separate value per input of `f_Y`, has the best mean of
the ordinary intervention on `Pa(Y)_𝒢`. -/
theorem bestE_inEdges (hG : G.WF) (m : Model n) (hm : ConfDiag G m) (r : m.X y → ℝ) :
    m.bestE y r (inEdges G y) = m.best y r (paSet G y) := by
  have hGd : m.scm.toMech.diag = G := hm
  -- the ordinary intervention on `Pa(Y)` as a specification
  have key : ∀ (x : ∀ i, m.X i) (u : ∀ l, m.U l), m.scm.toMech.resp (paSet G y) x u y =
      m.scm.toMech.respE (inEdges G y) (fun _ j => x j) u y := by
    intro x u
    rw [Mech.resp_eq_respE (paSet G y) x u (y_not_mem_paSet hG), hGd,
      ← relevant_outE_paSet hG, respE_relevant hGd]
  -- an assignment of `inEdges G y` is read only at `y`
  have key2 : ∀ (c : Fin n → ∀ p, m.X p) (u : ∀ l, m.U l),
      m.scm.toMech.respE (inEdges G y) c u y =
        m.scm.toMech.respE (inEdges G y) (fun _ j => c y j) u y := by
    intro c u
    have h := Mech.respE_congr (M := m.scm.toMech) (F := inEdges G y) (c := c)
      (c' := fun _ j => c y j) u (fun p v hpv => by rw [(POMISAux.mem_inEdges.mp hpv).2])
    rw [h]
  apply le_antisymm
  · apply m.bestE_le
    intro c
    have h1 : m.muE y r (inEdges G y) c = m.mu y r (paSet G y) (c y) := by
      unfold Model.muE Model.mu
      exact m.scm.E_congr (fun u => by rw [key2 c u, key (c y) u])
    rw [h1]
    exact m.mu_le_best y r _ (c y)
  · obtain ⟨x, hx⟩ := m.exists_best y r (paSet G y)
    have h2 : m.mu y r (paSet G y) x = m.muE y r (inEdges G y) (fun _ j => x j) := by
      unfold Model.muE Model.mu
      exact m.scm.E_congr (fun u => by rw [key x u])
    rw [← hx, h2]
    exact m.muE_le_bestE y r _ _

/-- **`prop: ctf-pomis unconfounded`**: if `Y` is not
confounded with `An(Y)_𝒢 ∖ {Y}`, the ordinary intervention set `Pa(Y)_𝒢` is the only ctf-POMIS
up to equivalence.  The ICLR's Prop. 2 omits "up to equivalence" (`ICLR.C5`). -/
theorem prop_unconfounded (hG : G.WF) (hnc : ∀ v, v ≠ y → G.Anc v y → G.bi y v = false)
    {F : EdgeSet n} :
    CtfPOMIS G y F ↔ relevant G y F = relevant G y (G.outE (paSet G y)) := by
  rw [ctfPomis_iff hG, relevant_outE_paSet hG]
  -- the minimal territory of `𝒢_F` is `{Y}`
  have hmuct : Alg.muct (G.cutE F) y ∅ = {y} := by
    have h := diagMUCT_singleton (POMISAux.wf_cutE hG F) (Finset.notMem_empty y)
      (fun v hv => by
        show G.bi y v = false
        by_cases hvy : v = y
        · rw [hvy]
          exact hG.bi_irrefl y
        · exact hnc v hvy (Reach.mono_rel (R := (G.cutE F).dir) (R' := G.dir)
            (fun a b _ hab => (ADMG.cutE_dir.mp hab).1) (BorderAux.mem_diagH_empty.mp hv)))
    exact (Alg.eq_muct h).symm
  -- so the border is empty exactly when every input of `f_Y` is selected
  have hIB : ctfIB G y F = ∅ ↔ ∀ v, G.dir v y = true → (v, y) ∈ F := by
    have hB : ctfIB G y F = diagBorder (G.cutE F) {y} := by
      show diagBorder (G.cutE F) (Alg.muct (G.cutE F) y ∅) = diagBorder (G.cutE F) {y}
      rw [hmuct]
    rw [hB]
    constructor
    · intro h v hv
      by_contra hvF
      have hvy : v ≠ y := fun e => by
        rw [e, hG.dir_irrefl] at hv
        exact Bool.false_ne_true hv
      have hmem : v ∈ diagBorder (G.cutE F) {y} :=
        Scb2018.mem_diagBorder.mpr ⟨fun h' => hvy (Finset.mem_singleton.mp h'), y,
          Finset.mem_singleton_self y, ADMG.cutE_dir.mpr ⟨hv, hvF⟩⟩
      rw [h] at hmem
      exact Finset.notMem_empty v hmem
    · intro hall
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨-, t, ht, hvt⟩ := Scb2018.mem_diagBorder.mp hv
      rw [Finset.mem_singleton] at ht
      rw [ht] at hvt
      exact (ADMG.cutE_dir.mp hvt).2 (hall v (ADMG.cutE_dir.mp hvt).1)
  rw [hIB]
  constructor
  · intro hall
    ext ⟨p, v⟩
    rw [BorderAux.mem_relevant, POMISAux.mem_inEdges, POMISAux.diagH_eq_singleton hall,
      Finset.mem_singleton]
    constructor
    · rintro ⟨-, h1, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1, h2⟩
      rw [h2] at h1 ⊢
      exact hall p h1
  · intro h v hv
    have hmem : (v, y) ∈ inEdges G y := POMISAux.mem_inEdges.mpr ⟨hv, rfl⟩
    rw [← h] at hmem
    exact relevant_subset G y F hmem

/-- **`cor: ctf-pomis markovian`**: in a Markovian diagram the ordinary
intervention set `Pa(Y)_𝒢` is the only ctf-POMIS up to equivalence. -/
theorem cor_markovian (hG : G.WF) (hmark : ∀ i j, G.bi i j = false) {F : EdgeSet n} :
    CtfPOMIS G y F ↔ relevant G y F = relevant G y (G.outE (paSet G y)) :=
  prop_unconfounded hG (fun v _ _ => hmark y v)

end Unconfounded

end Mec.CtfScb

import MecLean.CtfScb.Defs

set_option linter.unusedSectionVars false

/-!
# Interventional borders and counterfactual specifications

Pruning fixed inputs that cannot reach the reward preserves reward and the interventional
border. Fixing the inputs across a nonempty border yields a specification whose optimized
reward is at least as large. These facts give the necessity statement, a specification
enumerator, and optimal-value preservation.
-/

open Finset

namespace Mec.CtfScb

open Mec Mec.ScbMec Mec.Scb2018

variable {n : ℕ}

/-! ## Pruning and territories (graph facts) -/

section Graph

variable {G : ADMG n} {y : Fin n} {F : EdgeSet n}

/-- Pruning only removes selected inputs. -/
theorem relevant_subset (G : ADMG n) (y : Fin n) (F : EdgeSet n) : relevant G y F ⊆ F :=
  Finset.filter_subset _ _

/-! Auxiliary lemmas of this file (membership in `relevant`, `hEdges` and `borderEdges`, transfer
of directed paths between graphs, and the copy model of `cor: ctf-pomis returns non equivalent
set`) are in the namespace `Mec.CtfScb.BorderAux`. -/

namespace BorderAux

theorem mem_relevant {p v : Fin n} :
    (p, v) ∈ relevant G y F ↔ (p, v) ∈ F ∧ G.dir p v = true ∧ v ∈ diagH (G.cutE F) y ∅ := by
  simp only [relevant, Finset.mem_filter]

theorem mem_hEdges {p v : Fin n} : (p, v) ∈ hEdges G y ↔ G.dir p v = true ∧ G.Anc v y := by
  simp only [hEdges, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_borderEdges {T : Finset (Fin n)} {p v : Fin n} :
    (p, v) ∈ borderEdges G F T ↔ (G.cutE F).dir p v = true ∧ p ∉ T ∧ v ∈ T := by
  simp only [borderEdges, Finset.mem_filter, Finset.mem_univ, true_and]

/-- `An(Y)_H` read through `diagH` with no intervention. -/
theorem mem_diagH_empty {H : ADMG n} {v : Fin n} : v ∈ diagH H y ∅ ↔ H.Anc v y := by
  rw [Scb2018.mem_diagH]
  exact ⟨fun h => h.2, fun h => ⟨Finset.notMem_empty v, h⟩⟩

/-- Selecting more inputs deletes more edges. -/
theorem cutE_mono_dir {F₁ F₂ : EdgeSet n} (h : F₁ ⊆ F₂) {a b : Fin n}
    (hab : (G.cutE F₂).dir a b = true) : (G.cutE F₁).dir a b = true :=
  ADMG.cutE_dir.mpr ⟨(ADMG.cutE_dir.mp hab).1, fun h' => (ADMG.cutE_dir.mp hab).2 (h h')⟩

/-- Into a vertex of `An(Y)_{𝒢_F}`, the graphs of `F` and of its pruning have the same edges. -/
theorem cutE_relevant_dir_iff {t w : Fin n} (hw : w ∈ diagH (G.cutE F) y ∅) :
    (G.cutE (relevant G y F)).dir t w = true ↔ (G.cutE F).dir t w = true := by
  rw [ADMG.cutE_dir, ADMG.cutE_dir]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hF => h2 (mem_relevant.mpr ⟨hF, h1, hw⟩)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hR => h2 (relevant_subset G y F hR)⟩

/-- A path transfers to another relation when every step into a vertex that reaches the end in
the new relation is a step of the new relation. -/
theorem reach_head_transfer {R R' : Fin n → Fin n → Bool} {D : Finset (Fin n)} {a b : Fin n}
    (h : Reach R D a b) (hR : ∀ x z, R x z = true → z ∉ D → Reach R' D z b → R' x z = true) :
    Reach R' D a b := by
  unfold Reach at h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Reach.refl _
  | @head x z hxz _ ih => exact Reach.head (hR x z hxz.1 hxz.2 ih) hxz.2 ih

/-- Membership in `S` propagates backwards along a path whose steps into `S` start in `S`. -/
theorem mem_of_reach_head {R : Fin n → Fin n → Bool} {D S : Finset (Fin n)} {a b : Fin n}
    (h : Reach R D a b) (hb : b ∈ S) (hS : ∀ x z, R x z = true → z ∉ D → z ∈ S → x ∈ S) :
    a ∈ S := by
  unfold Reach at h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hb
  | @head x z hxz _ ih => exact hS x z hxz.1 hxz.2 ih

/-- A path from `S` whose steps from `S` stay in `S` transfers to another relation. -/
theorem reach_tail_transfer {R R' : Fin n → Fin n → Bool} {D D' S : Finset (Fin n)}
    {a b : Fin n} (h : Reach R D a b) (ha : a ∈ S)
    (hR : ∀ x z, x ∈ S → R x z = true → z ∉ D → R' x z = true ∧ z ∉ D' ∧ z ∈ S) :
    Reach R' D' a b ∧ b ∈ S := by
  induction h with
  | refl => exact ⟨Reach.refl _, ha⟩
  | @tail x z _ hxz ih =>
    obtain ⟨h1, h2, h3⟩ := hR x z ih.2 hxz.1 hxz.2
    exact ⟨Reach.tail ih.1 h1 h2, h3⟩

end BorderAux

/-- A retained input enters a reward ancestor, so it is an edge of `𝒢[An(Y)_𝒢]`. -/
theorem relevant_subset_hEdges (G : ADMG n) (y : Fin n) (F : EdgeSet n) :
    relevant G y F ⊆ hEdges G y := by
  rintro ⟨p, v⟩ he
  obtain ⟨-, hdir, hH⟩ := BorderAux.mem_relevant.mp he
  rw [BorderAux.mem_hEdges]
  exact ⟨hdir, Reach.mono_rel (R := (G.cutE F).dir) (R' := G.dir)
    (fun a b _ hab => (ADMG.cutE_dir.mp hab).1) (BorderAux.mem_diagH_empty.mp hH)⟩

/-- Pruning does not change the reward ancestors: a restored edge enters a vertex that is not an
ancestor of `y` in `𝒢_F`, so it starts no new path to `y` (proof of
`thm: enumerating ctf-pomis`). -/
theorem diagH_cutE_relevant (G : ADMG n) (y : Fin n) (F : EdgeSet n) :
    diagH (G.cutE (relevant G y F)) y ∅ = diagH (G.cutE F) y ∅ := by
  ext v
  rw [BorderAux.mem_diagH_empty, BorderAux.mem_diagH_empty]
  constructor
  · intro h
    exact BorderAux.reach_head_transfer (R := (G.cutE (relevant G y F)).dir)
      (R' := (G.cutE F).dir) h (fun x z hxz _ hz =>
        (BorderAux.cutE_relevant_dir_iff (BorderAux.mem_diagH_empty.mpr hz)).mp hxz)
  · intro h
    exact Reach.mono_rel (R := (G.cutE F).dir) (R' := (G.cutE (relevant G y F)).dir)
      (fun x z _ hxz => BorderAux.cutE_mono_dir (relevant_subset G y F) hxz) h

/-- A pruned specification is its own pruning, so `alg: ctf-pomis` returns each retained
specification as it is. -/
theorem relevant_relevant (G : ADMG n) (y : Fin n) (F : EdgeSet n) :
    relevant G y (relevant G y F) = relevant G y F := by
  ext ⟨p, v⟩
  constructor
  · intro h
    exact (BorderAux.mem_relevant.mp h).1
  · intro h
    refine BorderAux.mem_relevant.mpr ⟨h, (BorderAux.mem_relevant.mp h).2.1, ?_⟩
    rw [diagH_cutE_relevant]
    exact (BorderAux.mem_relevant.mp h).2.2

/-- Pruning does not change the regime graph `𝓗_{𝐗_{∗∗}}`, hence not its border. -/
theorem ctfIB_relevant (G : ADMG n) (y : Fin n) (F : EdgeSet n) :
    ctfIB G y (relevant G y F) = ctfIB G y F := by
  have hH := diagH_cutE_relevant G y F
  have hmuct : Alg.muct (G.cutE (relevant G y F)) y ∅ = Alg.muct (G.cutE F) y ∅ := by
    ext v
    rw [Alg.mem_muct, Alg.mem_muct, hH]
    constructor
    · intro h
      refine Reach.mono_rel (R := Alg.terrRel (G.cutE (relevant G y F)))
        (R' := Alg.terrRel (G.cutE F)) (fun a b hb hab => ?_) h
      have hbH : b ∈ diagH (G.cutE F) y ∅ := by simpa using hb
      rcases Alg.terrRel_iff.mp hab with h1 | h1
      · exact Alg.terrRel_iff.mpr (Or.inl ((BorderAux.cutE_relevant_dir_iff hbH).mp h1))
      · exact Alg.terrRel_iff.mpr (Or.inr h1)
    · intro h
      refine Reach.mono_rel (R := Alg.terrRel (G.cutE F))
        (R' := Alg.terrRel (G.cutE (relevant G y F))) (fun a b hb hab => ?_) h
      have hbH : b ∈ diagH (G.cutE F) y ∅ := by simpa using hb
      rcases Alg.terrRel_iff.mp hab with h1 | h1
      · exact Alg.terrRel_iff.mpr (Or.inl ((BorderAux.cutE_relevant_dir_iff hbH).mpr h1))
      · exact Alg.terrRel_iff.mpr (Or.inr h1)
  show diagBorder (G.cutE (relevant G y F)) (Alg.muct (G.cutE (relevant G y F)) y ∅) =
    diagBorder (G.cutE F) (Alg.muct (G.cutE F) y ∅)
  rw [hmuct]
  have hsub : Alg.muct (G.cutE F) y ∅ ⊆ diagH (G.cutE F) y ∅ :=
    Alg.muct_subset_diagH (Finset.notMem_empty y)
  ext v
  rw [Scb2018.mem_diagBorder, Scb2018.mem_diagBorder]
  constructor
  · rintro ⟨hv, t, ht, hvt⟩
    exact ⟨hv, t, ht, (BorderAux.cutE_relevant_dir_iff (hsub ht)).mp hvt⟩
  · rintro ⟨hv, t, ht, hvt⟩
    exact ⟨hv, t, ht, (BorderAux.cutE_relevant_dir_iff (hsub ht)).mpr hvt⟩

/-- Every edge of `𝒢` from outside `An(Y)_{𝒢_F}` into it is selected. -/
theorem mem_of_dir_into_diagH {p v : Fin n} (hv : v ∈ diagH (G.cutE F) y ∅)
    (hpv : G.dir p v = true) (hp : p ∉ diagH (G.cutE F) y ∅) : (p, v) ∈ F := by
  by_contra hpF
  exact hp (BorderAux.mem_diagH_empty.mpr
    (Reach.head (ADMG.cutE_dir.mpr ⟨hpv, hpF⟩) (Finset.notMem_empty v)
      (BorderAux.mem_diagH_empty.mp hv)))

/-- With an empty border, the minimal territory is the whole regime graph (`thm: ctf-pomis`,
"if"). -/
theorem muct_eq_diagH_of_ctfIB (h : ctfIB G y F = ∅) :
    Alg.muct (G.cutE F) y ∅ = diagH (G.cutE F) y ∅ := by
  refine Finset.Subset.antisymm (Alg.muct_subset_diagH (Finset.notMem_empty y))
    (fun v hv => ?_)
  have hB : diagBorder (G.cutE F) (Alg.muct (G.cutE F) y ∅) = ∅ := h
  refine BorderAux.mem_of_reach_head (R := (G.cutE F).dir) (BorderAux.mem_diagH_empty.mp hv)
    (Alg.mem_muct.mpr (Reach.refl y)) (fun a b hab _ hb => ?_)
  by_contra ha
  have hmem : a ∈ diagBorder (G.cutE F) (Alg.muct (G.cutE F) y ∅) :=
    Scb2018.mem_diagBorder.mpr ⟨ha, b, hb, hab⟩
  rw [hB] at hmem
  exact Finset.notMem_empty a hmem

namespace BorderAux

/-- The graph after fixing the inputs from outside `T` into `T`. -/
theorem cutE_union_borderEdges_dir {T : Finset (Fin n)} {a b : Fin n} :
    (G.cutE (F ∪ borderEdges G F T)).dir a b = true ↔
      (G.cutE F).dir a b = true ∧ (a ∈ T ∨ b ∉ T) := by
  simp only [ADMG.cutE_dir, Finset.mem_union, mem_borderEdges]
  tauto

/-- After fixing the inputs from the border of a UC-territory `T` into `T`, the reward ancestors
are `T` (the edge analogue of `Scb2018.diagH_border`). -/
theorem diagH_union_borderEdges {T : Finset (Fin n)} (hT : DiagUCT (G.cutE F) y ∅ T) :
    diagH (G.cutE (F ∪ borderEdges G F T)) y ∅ = T := by
  ext v
  rw [mem_diagH_empty]
  constructor
  · intro h
    refine mem_of_reach_head (R := (G.cutE (F ∪ borderEdges G F T)).dir) h hT.2.1
      (fun a b hab _ hb => ?_)
    rcases (cutE_union_borderEdges_dir.mp hab).2 with ha | hb'
    · exact ha
    · exact absurd hb hb'
  · intro hv
    refine (reach_tail_transfer (R' := (G.cutE (F ∪ borderEdges G F T)).dir) (D' := ∅)
      (Alg.reach_in_terr hT hv) hv (fun a b ha hab hb => ?_)).1
    have hbT : b ∈ T := by simpa using hb
    exact ⟨cutE_union_borderEdges_dir.mpr ⟨hab, Or.inl ha⟩, Finset.notMem_empty b, hbT⟩

end BorderAux

/-- Fixing the inputs from the border into the minimal territory `T` leaves `T` as the reward
ancestors, as the minimal territory, and an empty border. -/
theorem union_borderEdges {T : Finset (Fin n)} (hT : DiagMUCT (G.cutE F) y ∅ T) :
    diagH (G.cutE (F ∪ borderEdges G F T)) y ∅ = T ∧
      Alg.muct (G.cutE (F ∪ borderEdges G F T)) y ∅ = T ∧ ctfIB G y (F ∪ borderEdges G F T) = ∅ := by
  have hH := BorderAux.diagH_union_borderEdges hT.1
  have hM : DiagMUCT (G.cutE (F ∪ borderEdges G F T)) y ∅ T := by
    refine ⟨⟨fun v hv => by rw [hH]; exact hv, hT.1.2.1,
      fun t _ w hw _ => by rw [hH] at hw; exact hw,
      fun t _ w hw _ => by rw [hH] at hw; exact hw⟩, fun T' hT' hne hU => hT.2 T' hT' hne ?_⟩
    have hT'T := Finset.mem_powerset.mp hT'
    refine ⟨hT'T.trans hT.1.1, hU.2.1, fun t ht w hw hdir => ?_, fun t ht w hw hbi => ?_⟩
    · have hwT : w ∈ T := hT.1.2.2.1 t (hT'T ht) w hw hdir
      exact hU.2.2.1 t ht w (by rw [hH]; exact hwT)
        (BorderAux.cutE_union_borderEdges_dir.mpr ⟨hdir, Or.inl (hT'T ht)⟩)
    · have hwT : w ∈ T := hT.1.2.2.2 t (hT'T ht) w hw hbi
      exact hU.2.2.2 t ht w (by rw [hH]; exact hwT) hbi
  have hmuct : Alg.muct (G.cutE (F ∪ borderEdges G F T)) y ∅ = T :=
    ((Alg.diagMUCT_iff (Finset.notMem_empty y)).mp hM).symm
  refine ⟨hH, hmuct, ?_⟩
  show diagBorder (G.cutE (F ∪ borderEdges G F T))
    (Alg.muct (G.cutE (F ∪ borderEdges G F T)) y ∅) = ∅
  rw [hmuct]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hvT, t, ht, hvt⟩ := Scb2018.mem_diagBorder.mp hv
  rcases (BorderAux.cutE_union_borderEdges_dir.mp hvt).2 with h | h
  · exact hvT h
  · exact h ht

/-- When the territory `T` has a nonempty border, fixing its inputs changes the pruned
specification: the new inputs enter `T`, which still reaches `y`. -/
theorem relevant_union_borderEdges_ne {T : Finset (Fin n)} (hT : DiagUCT (G.cutE F) y ∅ T)
    (hne : diagBorder (G.cutE F) T ≠ ∅) :
    relevant G y (F ∪ borderEdges G F T) ≠ relevant G y F := by
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨hpT, t, ht, hpt⟩ := Scb2018.mem_diagBorder.mp hp
  intro hrel
  have hmem : (p, t) ∈ relevant G y (F ∪ borderEdges G F T) := by
    rw [BorderAux.mem_relevant, BorderAux.diagH_union_borderEdges hT]
    exact ⟨Finset.mem_union_right _ (BorderAux.mem_borderEdges.mpr ⟨hpt, hpT, ht⟩),
      (ADMG.cutE_dir.mp hpt).1, ht⟩
  rw [hrel] at hmem
  exact (ADMG.cutE_dir.mp hpt).2 (relevant_subset G y F hmem)

end Graph

/-! ## Semantics of pruning and of the border -/

section Semantic

variable {G : ADMG n} {y : Fin n}

/-- Removing the selected inputs at mechanisms outside the ancestral graph preserves the reward on
every unit (proof of `thm: enumerating ctf-pomis`). -/
theorem respE_relevant {Ω : Fin n → Type} {L : Type} {U : L → Type} [DecidableEq L]
    [∀ i, Inhabited (Ω i)] {M : Mech n Ω L U} (hM : M.diag = G) (F : EdgeSet n)
    (c : Fin n → ∀ p, Ω p) (u : ∀ l, U l) :
    M.respE (relevant G y F) c u y = M.respE F c u y := by
  symm
  refine Mech.respE_restrict (relevant_subset G y F) c u (fun p v hpF hpR hpa hanc => ?_)
  rw [hM] at hanc
  have hdir : G.dir p v = true := by
    rw [← hM]
    exact (M.diag_dir).mpr hpa
  have hvH : v ∈ diagH (G.cutE F) y ∅ := by
    rw [← diagH_cutE_relevant G y F]
    exact BorderAux.mem_diagH_empty.mpr hanc
  exact hpR (BorderAux.mem_relevant.mpr ⟨hpF, hdir, hvH⟩)

/-- Equal pruned specifications have equal best means. -/
theorem bestE_relevant (m : Model n) (hm : ConfDiag G m) (r : m.X y → ℝ) (F : EdgeSet n) :
    m.bestE y r (relevant G y F) = m.bestE y r F := by
  have hGd : m.scm.toMech.diag = G := hm
  unfold Model.bestE
  congr 1
  funext c
  exact m.muE_congr (fun u => respE_relevant hGd F c u)

/-- **Border mixture** (`thm: ctf-pomis`, "only if"): for a
UC-territory `T` of `𝒢_F` and a model conforming to `𝒢`, every assignment of `F` is matched by
the best assignment of `F` together with the inputs from the border into `T`.  Edge form of
`Scb2018.mu_le_best_diagBorder`; the independence of the territory's roots from those of the
border's ancestors is the block independence of. -/
theorem muE_le_bestE_border {F : EdgeSet n} {T : Finset (Fin n)}
    (hT : DiagUCT (G.cutE F) y ∅ T) (m : Model n) (hm : ConfDiag G m) (r : m.X y → ℝ)
    (c : Fin n → ∀ p, m.X p) : m.muE y r F c ≤ m.bestE y r (F ∪ borderEdges G F T) := by
  have hGd : m.scm.toMech.diag = G := hm
  -- the roots that no vertex of the territory reads
  obtain ⟨D, hD⟩ : ∃ D : Finset m.L, ∀ l, l ∈ D ↔ ∀ t ∈ T, l ∉ m.scm.toMech.ex t :=
    ⟨Finset.univ.filter (fun l => ∀ t ∈ T, l ∉ m.scm.toMech.ex t),
      fun l => by rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]⟩
  -- the new inputs receive the values of their sources in the world of `F`
  obtain ⟨c', hc'⟩ : ∃ c' : (∀ l, m.U l) → Fin n → ∀ p, m.X p, ∀ u v p,
      c' u v p = if (p, v) ∈ F then c v p else m.scm.toMech.respE F c u p :=
    ⟨fun u v p => if (p, v) ∈ F then c v p else m.scm.toMech.respE F c u p,
      fun _ _ _ => rfl⟩
  -- composition
  have hcons : ∀ u, m.scm.toMech.respE F c u y =
      m.scm.toMech.respE (F ∪ borderEdges G F T) (c' u) u y := by
    intro u
    have h1 : m.scm.toMech.respE (F ∪ borderEdges G F T) (c' u) u =
        m.scm.toMech.respE F c u :=
      Mech.respE_extend Finset.subset_union_left c (c' u) u
        (fun p v hpv => by rw [hc', ite_eq_left hpv])
        (fun p v _ hpv => by rw [hc', ite_eq_right hpv])
    rw [h1]
  -- the ancestors of the sources of the new inputs lie in `An(Y)_{𝒢_F}` outside `T`
  have hB : ∀ p v, (p, v) ∈ F ∪ borderEdges G F T → (p, v) ∉ F → ∀ w,
      (G.cutE F).Anc w p → w ∈ diagH (G.cutE F) y ∅ ∧ w ∉ T := by
    intro p v hpv hpF w hwp
    obtain ⟨hdir, hpT, hvT⟩ :=
      BorderAux.mem_borderEdges.mp ((Finset.mem_union.mp hpv).resolve_left hpF)
    have hpH : p ∈ diagH (G.cutE F) y ∅ := BorderAux.mem_diagH_empty.mpr
      (Reach.head hdir (Finset.notMem_empty v) (BorderAux.mem_diagH_empty.mp (hT.1 hvT)))
    refine ⟨BorderAux.mem_diagH_empty.mpr
      (Reach.trans hwp (BorderAux.mem_diagH_empty.mp hpH)), fun hwT => hpT ?_⟩
    exact Scb2018.diag_desc_closed hT hwT hwp hpH
  -- the territory reads no root of `D`
  have hTD : ∀ w, (m.scm.toMech.diag.cutE (F ∪ borderEdges G F T)).Anc w y →
      ∀ l ∈ m.scm.toMech.ex w, l ∉ D := by
    intro w hw l hl hlD
    rw [hGd] at hw
    have hwH : w ∈ diagH (G.cutE (F ∪ borderEdges G F T)) y ∅ :=
      BorderAux.mem_diagH_empty.mpr hw
    rw [BorderAux.diagH_union_borderEdges hT] at hwH
    exact (hD l).mp hlD w hwH hl
  -- the new inputs read only roots of `D`
  have hBD : ∀ p v, (p, v) ∈ F ∪ borderEdges G F T → (p, v) ∉ F → ∀ w,
      (m.scm.toMech.diag.cutE F).Anc w p → ∀ l ∈ m.scm.toMech.ex w, l ∈ D := by
    intro p v hpv hpF w hwp l hl
    rw [hGd] at hwp
    obtain ⟨hwH, hwT⟩ := hB p v hpv hpF w hwp
    refine (hD l).mpr (fun t ht hlt => hwT ?_)
    have hbi : m.scm.toMech.diag.bi t w = true := by
      simp only [Mech.diag, decide_eq_true_eq]
      exact ⟨fun e => hwT (e ▸ ht), l, Finset.mem_inter.mpr ⟨hlt, hl⟩⟩
    rw [hGd] at hbi
    exact hT.2.2.2 t ht w hwH hbi
  have hsplit : ∀ a b : (∀ l, m.U l),
      r (m.scm.toMech.respE F c (SCM.merge D a b) y) =
        r (m.scm.toMech.respE (F ∪ borderEdges G F T) (c' a) b y) := by
    intro a b
    rw [hcons]
    congr 1
    have e1 : m.scm.toMech.respE (F ∪ borderEdges G F T) (c' (SCM.merge D a b))
        (SCM.merge D a b) =
        m.scm.toMech.respE (F ∪ borderEdges G F T) (c' a) (SCM.merge D a b) := by
      apply Mech.respE_congr
      intro p v hpv
      rw [hc', hc']
      by_cases hpF : (p, v) ∈ F
      · rw [ite_eq_left hpF, ite_eq_left hpF]
      · rw [ite_eq_right hpF, ite_eq_right hpF]
        apply Mech.respE_roots
        intro w hwp l hl
        exact SCM.merge_of_mem (hBD p v hpv hpF w hwp l hl)
    rw [e1]
    apply Mech.respE_roots
    intro w hwy l hl
    exact SCM.merge_of_not_mem (hTD w hwy l hl)
  have hE : m.muE y r F c = ∑ a : (∀ l, m.U l), m.scm.prob a *
      m.muE y r (F ∪ borderEdges G F T) (c' a) := by
    unfold Model.muE
    exact m.scm.E_split D _
      (fun a b => r (m.scm.toMech.respE (F ∪ borderEdges G F T) (c' a) b y)) hsplit
  rw [hE]
  calc ∑ a : (∀ l, m.U l), m.scm.prob a * m.muE y r (F ∪ borderEdges G F T) (c' a)
      ≤ ∑ a : (∀ l, m.U l), m.scm.prob a * m.bestE y r (F ∪ borderEdges G F T) :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left
          (m.muE_le_bestE y r _ (c' a)) (m.scm.prob_nonneg a))
    _ = m.bestE y r (F ∪ borderEdges G F T) := by
        rw [← Finset.sum_mul, m.scm.sum_prob, one_mul]

/-- The border mixture for the best assignments, `μ_{𝐗_{∗∗}^∗} ≤ μ_{𝐗'^∗_{∗∗}}`. -/
theorem bestE_le_bestE_border {F : EdgeSet n} {T : Finset (Fin n)}
    (hT : DiagUCT (G.cutE F) y ∅ T) (m : Model n) (hm : ConfDiag G m) (r : m.X y → ℝ) :
    m.bestE y r F ≤ m.bestE y r (F ∪ borderEdges G F T) := by
  obtain ⟨c, hc⟩ := m.exists_bestE y r F
  rw [← hc]
  exact muE_le_bestE_border hT m hm r c

end Semantic

/-! ## `thm: ctf-pomis`, "only if" -/

/-- **`thm: ctf-pomis`, "only if"**: a ctf-POMIS has an empty
border.  Otherwise fixing the inputs from the border into the minimal territory gives a
non-equivalent specification that is at least as good in every model conforming to `𝒢`
(`muE_le_bestE_border`, `relevant_union_borderEdges_ne`); no copy SCM is needed. -/
theorem ctfPomis_onlyif {G : ADMG n} (hG : G.WF) {y : Fin n} {F : EdgeSet n}
    (h : CtfPOMIS G y F) : ctfIB G y F = ∅ := by
  by_contra hne
  have hT : DiagUCT (G.cutE F) y ∅ (Alg.muct (G.cutE F) y ∅) :=
    Alg.diagUCT_muct (Finset.notMem_empty y)
  obtain ⟨m, r, hm, hbest⟩ := h
  have h1 := hbest _ (relevant_union_borderEdges_ne hT hne)
  have h2 := bestE_le_bestE_border hT m hm r
  linarith

/-! ## The copy model of `cor: ctf-pomis returns non equivalent set` -/

namespace BorderAux

/-- The copy equations: the source `s` outputs its private root, `v` copies its input from `s`, a
vertex of `A` other than `v` is the OR of its inputs from `A` along edges of `K`, and every other
vertex is `false`. -/
def copyF (K : ADMG n) (A : Finset (Fin n)) (s v i : Fin n) (z : Fin n → Bool)
    (u : Roots n → Bool) : Bool :=
  if i = s then u (Sum.inl s) else if i = v then z s else
    decide (i ∈ A ∧ ∃ q, q ∈ A ∧ K.dir q i = true ∧ z q = true)

theorem copyF_src (K : ADMG n) (A : Finset (Fin n)) (s v : Fin n) (z : Fin n → Bool)
    (u : Roots n → Bool) : copyF K A s v s z u = u (Sum.inl s) := by
  unfold copyF
  exact ite_eq_left rfl

theorem copyF_tgt (K : ADMG n) (A : Finset (Fin n)) {s v : Fin n} (hvs : v ≠ s)
    (z : Fin n → Bool) (u : Roots n → Bool) : copyF K A s v v z u = z s := by
  unfold copyF
  rw [ite_eq_right hvs, ite_eq_left rfl]

theorem copyF_other (K : ADMG n) (A : Finset (Fin n)) {s v i : Fin n} (his : i ≠ s)
    (hiv : i ≠ v) (z : Fin n → Bool) (u : Roots n → Bool) :
    copyF K A s v i z u = decide (i ∈ A ∧ ∃ q, q ∈ A ∧ K.dir q i = true ∧ z q = true) := by
  unfold copyF
  rw [ite_eq_right his, ite_eq_right hiv]

theorem copyF_pa {G K : ADMG n} (hK : ∀ a b, K.dir a b = true → G.dir a b = true)
    (A : Finset (Fin n)) {s v : Fin n} (hsv : G.dir s v = true) (i : Fin n)
    (x x' : Fin n → Bool) (u : Roots n → Bool) (h : ∀ j, G.dir j i = true → x j = x' j) :
    copyF K A s v i x u = copyF K A s v i x' u := by
  by_cases his : i = s
  · rw [his, copyF_src, copyF_src]
  · by_cases hiv : i = v
    · have hvs : v ≠ s := fun e => his (hiv.trans e)
      have hsi : G.dir s i = true := by
        rw [hiv]
        exact hsv
      rw [hiv, copyF_tgt K A hvs, copyF_tgt K A hvs]
      exact h s hsi
    · rw [copyF_other K A his hiv, copyF_other K A his hiv]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_iff]
      exact and_congr_right (fun _ => exists_congr (fun q => and_congr_right (fun _ =>
        and_congr_right (fun hq => by rw [h q (hK q i hq)]))))

theorem copyF_ex (G K : ADMG n) (A : Finset (Fin n)) (s v i : Fin n) (x : Fin n → Bool)
    (u u' : Roots n → Bool) (h : ∀ l ∈ rootScope G i, u l = u' l) :
    copyF K A s v i x u = copyF K A s v i x u' := by
  by_cases his : i = s
  · rw [his, copyF_src, copyF_src]
    rw [his] at h
    exact h _ (mem_rootScope.mpr (Or.inl rfl))
  · unfold copyF
    rw [ite_eq_right his, ite_eq_right his]

/-- The copy mechanisms; their causal diagram is `G`. -/
def copyMech (G : ADMG n) (hG : G.WF) (K : ADMG n)
    (hK : ∀ a b, K.dir a b = true → G.dir a b = true) (A : Finset (Fin n)) (s v : Fin n)
    (hsv : G.dir s v = true) : Mech n (fun _ => Bool) (Roots n) (fun _ => Bool) :=
  Mech.ofADMG G hG (copyF K A s v) (copyF_pa hK A hsv) (copyF_ex G K A s v)

/-- The copy SCM: every root is a fair coin. -/
noncomputable def copySCM (G : ADMG n) (hG : G.WF) (K : ADMG n)
    (hK : ∀ a b, K.dir a b = true → G.dir a b = true) (A : Finset (Fin n)) (s v : Fin n)
    (hsv : G.dir s v = true) : SCM n (fun _ => Bool) (Roots n) (fun _ => Bool) where
  toMech := copyMech G hG K hK A s v hsv
  p _ _ := 1 / 2
  p_nonneg _ _ := by norm_num
  p_sum _ := by norm_num [Fintype.sum_bool]

/-- The copy model. -/
noncomputable def copyModel (G : ADMG n) (hG : G.WF) (K : ADMG n)
    (hK : ∀ a b, K.dir a b = true → G.dir a b = true) (A : Finset (Fin n)) (s v : Fin n)
    (hsv : G.dir s v = true) : Model n where
  X := fun _ => Bool
  L := Roots n
  U := fun _ => Bool
  scm := copySCM G hG K hK A s v hsv

theorem copyModel_conf (G : ADMG n) (hG : G.WF) (K : ADMG n)
    (hK : ∀ a b, K.dir a b = true → G.dir a b = true) (A : Finset (Fin n)) (s v : Fin n)
    (hsv : G.dir s v = true) : ConfDiag G (copyModel G hG K hK A s v hsv) := by
  show (copyMech G hG K hK A s v hsv).diag = G
  exact Mech.ofADMG_diag G hG _ _ _

/-- Under a specification that fixes no edge of `K`, every vertex of `A` takes the value that
`v` receives from `s`. -/
theorem copy_respE {G : ADMG n} (hG : G.WF) {K : ADMG n}
    (hK : ∀ a b, K.dir a b = true → G.dir a b = true) {A : Finset (Fin n)} {s v : Fin n}
    (hsv : G.dir s v = true) (hsA : s ∉ A) (hvA : v ∈ A)
    (hA : ∀ w ∈ A, w ≠ v → ∃ q, q ∈ A ∧ K.dir q w = true)
    {R : EdgeSet n} (hR : ∀ q w, K.dir q w = true → (q, w) ∉ R) (c : Fin n → Fin n → Bool)
    (u : Roots n → Bool) {b : Bool} (hb : (if (s, v) ∈ R then c v s else u (Sum.inl s)) = b)
    {w : Fin n} (hw : w ∈ A) : (copyMech G hG K hK A s v hsv).respE R c u w = b := by
  have hvs : v ≠ s := fun e => hsA (e ▸ hvA)
  obtain ⟨z, hz⟩ : ∃ z : Fin n → Bool, ∀ i,
      z i = if i = s then u (Sum.inl s) else if i ∈ A then b else false :=
    ⟨fun i => if i = s then u (Sum.inl s) else if i ∈ A then b else false, fun _ => rfl⟩
  have hzs : z s = u (Sum.inl s) := by rw [hz, ite_eq_left rfl]
  have hzA : ∀ i ∈ A, z i = b := by
    intro i hi
    have his : i ≠ s := fun e => hsA (e ▸ hi)
    rw [hz, ite_eq_right his, ite_eq_left hi]
  have hzo : ∀ i, i ≠ s → i ∉ A → z i = false := fun i his hiA => by
    rw [hz, ite_eq_right his, ite_eq_right hiA]
  have hsol : z = (copyMech G hG K hK A s v hsv).respE R c u := by
    apply Mech.eq_respE
    intro i
    show z i = copyF K A s v i (fun j => if (j, i) ∈ R then c i j else z j) u
    by_cases his : i = s
    · rw [his, hzs, copyF_src]
    · by_cases hiv : i = v
      · rw [hiv, hzA v hvA, copyF_tgt K A hvs]
        show b = if (s, v) ∈ R then c v s else z s
        rw [hzs]
        exact hb.symm
      · rw [copyF_other K A his hiv]
        by_cases hiA : i ∈ A
        · rw [hzA i hiA]
          obtain ⟨q, hqA, hqi⟩ := hA i hiA hiv
          have hiff : (i ∈ A ∧ ∃ q, q ∈ A ∧ K.dir q i = true ∧
              (if (q, i) ∈ R then c i q else z q) = true) ↔ b = true := by
            constructor
            · rintro ⟨-, q', hq'A, hq'i, hq'⟩
              rw [ite_eq_right (hR q' i hq'i), hzA q' hq'A] at hq'
              exact hq'
            · intro hbt
              refine ⟨hiA, q, hqA, hqi, ?_⟩
              rw [ite_eq_right (hR q i hqi), hzA q hqA]
              exact hbt
          cases b with
          | false => exact Eq.symm (decide_eq_false (fun h => Bool.false_ne_true (hiff.mp h)))
          | true => exact Eq.symm (decide_eq_true (hiff.mpr rfl))
        · rw [hzo i his hiA]
          exact Eq.symm (decide_eq_false (fun h => hiA h.1))
  rw [← congrFun hsol w]
  exact hzA w hw

/-- **Copy model.**  If `s → v` is selected by `R₁` but not by `R₂`, and `v` reaches `y` along
edges selected by neither, then in a binary model conforming to `G` some assignment of `R₁`
differs on some unit from every assignment of `R₂`: under `R₁` the reward copies the constant
received by `v`, under `R₂` it copies the private coin of `s`. -/
theorem copy_sep {G : ADMG n} {y : Fin n} (hG : G.WF) {R₁ R₂ : EdgeSet n} {s v : Fin n}
    (hsv : G.dir s v = true) (h1 : (s, v) ∈ R₁) (h2 : (s, v) ∉ R₂)
    (hpath : Reach (G.cutE (R₁ ∪ R₂)).dir ∅ v y) :
    ∃ m : Model n, ConfDiag G m ∧ ∃ c₁ : Fin n → ∀ p, m.X p, ∀ c₂ : Fin n → ∀ p, m.X p,
      ∃ u : ∀ l, m.U l, m.scm.toMech.respE R₁ c₁ u y ≠ m.scm.toMech.respE R₂ c₂ u y := by
  have hK : ∀ a b, (G.cutE (R₁ ∪ R₂)).dir a b = true → G.dir a b = true :=
    fun a b hab => (ADMG.cutE_dir.mp hab).1
  obtain ⟨A, hA⟩ : ∃ A : Finset (Fin n), ∀ w, w ∈ A ↔
      Reach (G.cutE (R₁ ∪ R₂)).dir ∅ v w ∧ Reach (G.cutE (R₁ ∪ R₂)).dir ∅ w y :=
    ⟨Finset.univ.filter (fun w => Reach (G.cutE (R₁ ∪ R₂)).dir ∅ v w ∧
      Reach (G.cutE (R₁ ∪ R₂)).dir ∅ w y), fun w => by
        rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]⟩
  have hyA : y ∈ A := (hA y).mpr ⟨hpath, Reach.refl y⟩
  have hvA : v ∈ A := (hA v).mpr ⟨Reach.refl v, hpath⟩
  have hsA : s ∉ A := fun hs => hG.acyclic hsv
    (Reach.mono_rel (R := (G.cutE (R₁ ∪ R₂)).dir) (R' := G.dir)
      (fun a b _ hab => hK a b hab) ((hA s).mp hs).1)
  have hpred : ∀ w ∈ A, w ≠ v → ∃ q, q ∈ A ∧ (G.cutE (R₁ ∪ R₂)).dir q w = true := by
    intro w hw hwv
    obtain ⟨hvw, hwy⟩ := (hA w).mp hw
    rcases Relation.ReflTransGen.cases_tail hvw with e | ⟨q, hvq, hqw⟩
    · exact absurd e hwv
    · exact ⟨q, (hA q).mpr ⟨hvq, Reach.head hqw.1 hqw.2 hwy⟩, hqw.1⟩
  have hR₁ : ∀ q w, (G.cutE (R₁ ∪ R₂)).dir q w = true → (q, w) ∉ R₁ :=
    fun q w hqw hq => (ADMG.cutE_dir.mp hqw).2 (Finset.mem_union_left _ hq)
  have hR₂ : ∀ q w, (G.cutE (R₁ ∪ R₂)).dir q w = true → (q, w) ∉ R₂ :=
    fun q w hqw hq => (ADMG.cutE_dir.mp hqw).2 (Finset.mem_union_right _ hq)
  refine ⟨copyModel G hG (G.cutE (R₁ ∪ R₂)) hK A s v hsv,
    copyModel_conf G hG (G.cutE (R₁ ∪ R₂)) hK A s v hsv, fun _ _ => true, fun c₂ => ?_⟩
  refine ⟨fun _ => false, fun hxy => ?_⟩
  have e1 : (copyMech G hG (G.cutE (R₁ ∪ R₂)) hK A s v hsv).respE R₁ (fun _ _ => true)
      (fun _ => false) y = true :=
    copy_respE hG hK hsv hsA hvA hpred hR₁ _ _ (by rw [ite_eq_left h1]) hyA
  have e2 : (copyMech G hG (G.cutE (R₁ ∪ R₂)) hK A s v hsv).respE R₂ c₂ (fun _ => false) y =
      false :=
    copy_respE hG hK hsv hsA hvA hpred hR₂ c₂ _ (by exact ite_eq_right h2) hyA
  have hc : (true : Bool) = false := e1.symm.trans (hxy.trans e2)
  exact Bool.false_ne_true hc.symm

/-- The last edge of `R₂` on a path of `𝒢_{R₁}`: either the path avoids `R₂` as well, or an
edge of `R₂ ∖ R₁` on it is followed by a path that avoids both. -/
theorem reach_last_edge {G : ADMG n} {R₁ R₂ : EdgeSet n} {a b : Fin n}
    (h : Reach (G.cutE R₁).dir ∅ a b) :
    Reach (G.cutE (R₁ ∪ R₂)).dir ∅ a b ∨ ∃ s v, (s, v) ∈ R₂ ∧ (s, v) ∉ R₁ ∧
      G.dir s v = true ∧ Reach (G.cutE (R₁ ∪ R₂)).dir ∅ v b := by
  induction h with
  | refl => exact Or.inl (Reach.refl _)
  | @tail c d _ hcd ih =>
    have hd := ADMG.cutE_dir.mp hcd.1
    by_cases hcd2 : (c, d) ∈ R₂
    · exact Or.inr ⟨c, d, hcd2, hd.2, hd.1, Reach.refl d⟩
    · have hstep : (G.cutE (R₁ ∪ R₂)).dir c d = true :=
        ADMG.cutE_dir.mpr ⟨hd.1, fun h' => (Finset.mem_union.mp h').elim hd.2 hcd2⟩
      rcases ih with ih | ⟨s, v, h1, h2, h3, h4⟩
      · exact Or.inl (Reach.tail ih hstep (Finset.notMem_empty d))
      · exact Or.inr ⟨s, v, h1, h2, h3, Reach.tail h4 hstep (Finset.notMem_empty d)⟩

/-- Two distinct pruned specifications are separated by an edge selected by exactly one of them
whose receiver reaches `y` along edges selected by neither (proof of `cor: ctf-pomis returns non
equivalent set`). -/
theorem exists_sep_edge {G : ADMG n} {y : Fin n} {F F' : EdgeSet n}
    (hne : relevant G y F ≠ relevant G y F') :
    ∃ s v, G.dir s v = true ∧ Reach (G.cutE (relevant G y F ∪ relevant G y F')).dir ∅ v y ∧
      ((s, v) ∈ relevant G y F ∧ (s, v) ∉ relevant G y F' ∨
        (s, v) ∈ relevant G y F' ∧ (s, v) ∉ relevant G y F) := by
  have hpath : ∀ {F₁ : EdgeSet n} {s v : Fin n}, (s, v) ∈ relevant G y F₁ →
      Reach (G.cutE (relevant G y F₁)).dir ∅ v y := by
    intro F₁ s v h
    exact Reach.mono_rel (R := (G.cutE F₁).dir) (R' := (G.cutE (relevant G y F₁)).dir)
      (fun a b _ hab => cutE_mono_dir (relevant_subset G y F₁) hab)
      (mem_diagH_empty.mp (mem_relevant.mp h).2.2)
  obtain ⟨⟨s, v⟩, he⟩ : ∃ e, (e ∈ relevant G y F ∧ e ∉ relevant G y F') ∨
      (e ∈ relevant G y F' ∧ e ∉ relevant G y F) := by
    by_contra hcon
    apply hne
    ext e
    constructor
    · intro h
      by_contra h'
      exact hcon ⟨e, Or.inl ⟨h, h'⟩⟩
    · intro h
      by_contra h'
      exact hcon ⟨e, Or.inr ⟨h, h'⟩⟩
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hsv := (mem_relevant.mp h1).2.1
    rcases reach_last_edge (R₂ := relevant G y F') (hpath h1) with
      hp | ⟨s', v', h1', h2', h3', h4'⟩
    · exact ⟨s, v, hsv, hp, Or.inl ⟨h1, h2⟩⟩
    · exact ⟨s', v', h3', h4', Or.inr ⟨h1', h2'⟩⟩
  · have hsv := (mem_relevant.mp h1).2.1
    rcases reach_last_edge (R₂ := relevant G y F) (hpath h1) with
      hp | ⟨s', v', h1', h2', h3', h4'⟩
    · rw [Finset.union_comm] at hp
      exact ⟨s, v, hsv, hp, Or.inr ⟨h1, h2⟩⟩
    · rw [Finset.union_comm] at h4'
      exact ⟨s', v', h3', h4', Or.inl ⟨h1', h2'⟩⟩

end BorderAux

/-! ## The output of `alg: ctf-pomis` -/

section Enumeration

variable {G : ADMG n} {y : Fin n}

/-- The output of `alg: ctf-pomis` in graph terms: the pruned specifications of
edges of `𝒢[An(Y)_𝒢]` with empty border. -/
theorem mem_ctfPOMISs_iff {F : EdgeSet n} :
    F ∈ ctfPOMISs G y ↔ relevant G y F = F ∧ F ⊆ hEdges G y ∧ ctfIB G y F = ∅ := by
  unfold ctfPOMISs
  rw [Finset.mem_image]
  constructor
  · rintro ⟨F₀, hF₀, rfl⟩
    rw [Finset.mem_filter, Finset.mem_powerset] at hF₀
    refine ⟨relevant_relevant G y F₀, relevant_subset_hEdges G y F₀, ?_⟩
    rw [ctfIB_relevant]
    exact hF₀.2
  · rintro ⟨h1, h2, h3⟩
    exact ⟨F, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h2, h3⟩, h1⟩

/-- Equal pruned specifications are equivalent, with the same values. -/
theorem specEquiv_of_relevant_eq {F F' : EdgeSet n} (h : relevant G y F = relevant G y F') :
    SpecEquiv G y F F' := by
  intro m hm
  have hGd : m.scm.toMech.diag = G := hm
  have key : ∀ (c : Fin n → ∀ p, m.X p) (u : ∀ l, m.U l),
      m.scm.toMech.respE F c u y = m.scm.toMech.respE F' c u y := by
    intro c u
    rw [← respE_relevant hGd F c u, ← respE_relevant hGd F' c u, h]
  exact ⟨fun c => ⟨c, fun u => key c u⟩, fun c' => ⟨c', fun u => key c' u⟩⟩

/-- Distinct pruned specifications are not equivalent: a binary copy SCM along an edge selected by
one of them and a path retained by both gives a constant reward under one and a fair coin under
the other (proof of `cor: ctf-pomis returns non equivalent set`). -/
theorem relevant_eq_of_specEquiv (hG : G.WF) {F F' : EdgeSet n} (h : SpecEquiv G y F F') :
    relevant G y F = relevant G y F' := by
  by_contra hne
  obtain ⟨s, v, hsv, hpath, hsep⟩ := BorderAux.exists_sep_edge hne
  rcases hsep with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨m, hm, c₁, hc⟩ := BorderAux.copy_sep hG hsv h1 h2 hpath
    have hGd : m.scm.toMech.diag = G := hm
    obtain ⟨c', hc'⟩ := (h m hm).1 c₁
    obtain ⟨u, hu⟩ := hc c'
    apply hu
    rw [respE_relevant hGd F c₁ u, respE_relevant hGd F' c' u]
    exact hc' u
  · rw [Finset.union_comm] at hpath
    obtain ⟨m, hm, c₁, hc⟩ := BorderAux.copy_sep hG hsv h1 h2 hpath
    have hGd : m.scm.toMech.diag = G := hm
    obtain ⟨c, hc'⟩ := (h m hm).2 c₁
    obtain ⟨u, hu⟩ := hc c
    apply hu
    rw [respE_relevant hGd F' c₁ u, respE_relevant hGd F c u]
    exact (hc' u).symm

/-- Equivalence of specifications is equality of the pruned specifications. -/
theorem specEquiv_iff_relevant_eq (hG : G.WF) {F F' : EdgeSet n} :
    SpecEquiv G y F F' ↔ relevant G y F = relevant G y F' :=
  ⟨relevant_eq_of_specEquiv hG, specEquiv_of_relevant_eq⟩

/-- **`cor: ctf-pomis returns non equivalent set`**: no two specifications
returned by `alg: ctf-pomis` are equivalent. -/
theorem ctfPOMISs_not_equiv (hG : G.WF) {F F' : EdgeSet n} (hF : F ∈ ctfPOMISs G y)
    (hF' : F' ∈ ctfPOMISs G y) (hne : F ≠ F') : ¬ SpecEquiv G y F F' := by
  intro h
  have h1 := (mem_ctfPOMISs_iff.mp hF).1
  have h2 := (mem_ctfPOMISs_iff.mp hF').1
  exact hne (h1.symm.trans ((relevant_eq_of_specEquiv hG h).trans h2))

/-- Every specification is weakly dominated, in a given model conforming to `𝒢`, by a returned one:
fix the inputs from its border into its minimal territory, then prune. -/
theorem exists_ctfPOMISs_ge (hG : G.WF) (m : Model n) (hm : ConfDiag G m) (r : m.X y → ℝ)
    (F' : EdgeSet n) : ∃ F ∈ ctfPOMISs G y, m.bestE y r F' ≤ m.bestE y r F := by
  have hT : DiagMUCT (G.cutE F') y ∅ (Alg.muct (G.cutE F') y ∅) :=
    Alg.diagMUCT_muct (Finset.notMem_empty y)
  obtain ⟨-, -, hIB⟩ := union_borderEdges hT
  refine ⟨relevant G y (F' ∪ borderEdges G F' (Alg.muct (G.cutE F') y ∅)), ?_, ?_⟩
  · rw [mem_ctfPOMISs_iff]
    refine ⟨relevant_relevant G y _, relevant_subset_hEdges G y _, ?_⟩
    rw [ctfIB_relevant]
    exact hIB
  · rw [bestE_relevant m hm r]
    exact bestE_le_bestE_border hT.1 m hm r

/-- **`cor: ctf-pomis action space preserves optimal reward`**: in every model conforming to `𝒢`, the best mean over `𝒜^⋆_ctf` equals the best mean
over `𝒜_ctf`, `ctfOpt`.  (`ctfPOMISs G y` consists of specifications, so the reverse inequality is
`Finset.le_sup'`.) -/
theorem ctfPOMISs_optimal (hG : G.WF) (m : Model n) (hm : ConfDiag G m) (r : m.X y → ℝ) :
    ∃ F ∈ ctfPOMISs G y, m.bestE y r F = ctfOpt m y r := by
  obtain ⟨F', -, hF'⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := EdgeSet n))
    (fun F => m.bestE y r F)
  obtain ⟨F, hF, hle⟩ := exists_ctfPOMISs_ge hG m hm r F'
  have hopt : ctfOpt m y r = m.bestE y r F' := hF'
  refine ⟨F, hF, le_antisymm ?_ ?_⟩
  · exact Finset.le_sup' (fun F => m.bestE y r F) (Finset.mem_univ F)
  · rw [hopt]
    exact hle

end Enumeration

end Mec.CtfScb

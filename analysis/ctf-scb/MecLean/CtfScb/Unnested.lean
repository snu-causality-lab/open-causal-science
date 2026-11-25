import MecLean.CtfScb.Misify

set_option linter.unusedSectionVars false

/-!
# Unnested counterfactual actions

The terms of an unnested action are evaluated in their respective submodels at the same unit.
Agreed computations can be expressed by a single parent-input specification. The
ancestral no-conflict test gives a sufficient condition for this representation.
-/

open Finset

namespace Mec.CtfScb

open Mec Mec.ScbMec

variable {n : ℕ}

namespace UCtf

variable {G : ADMG n} {A : UCtf n} {y : Fin n}

/-! ### Auxiliary lemmas -/

theorem mem_specOf {p v : Fin n} :
    (p, v) ∈ A.specOf G ↔ ∃ i ∈ A.tgt, p ∈ A.sub i ∧ G.dir p v = true ∧ v ∈ A.comp G i := by
  unfold UCtf.specOf
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

theorem msub_subset {i v : Fin n} : A.msub G i v ⊆ A.sub i := by
  unfold UCtf.msub
  exact Finset.filter_subset _ _

/-- The source of an edge of `𝒢` from `𝐖_i` into the computation of `X_i` is in the minimized
subscript of its receiver. -/
theorem mem_msub_of_dir {i p v : Fin n} (hp : p ∈ A.sub i) (hpv : G.dir p v = true)
    (hv : v ∈ A.comp G i) : p ∈ A.msub G i v := by
  unfold UCtf.msub
  exact Finset.mem_filter.mpr ⟨hp, Reach.single hpv (Scb2018.mem_diagH.mp hv).1⟩

/-- When the targets' computations use the same minimized subscript variables, a directed path of
`𝒢` from the computation of `X_i` to `X_i` that avoids `𝐖_i` selects no input of `specOf G A`:
an edge `a → b` selected by the computation of `X_j` has `a` in the minimized subscript of `b`
for `X_j`, hence for `X_i`, so `a ∈ 𝐖_i`. -/
theorem ancAvoid_cutE_specOf (h : A.SameVars G) {i : Fin n} (hi : i ∈ A.tgt)
    {D : Finset (Fin n)} (hD : A.sub i ⊆ D) :
    ∀ w, G.AncAvoid D w i → w ∉ A.sub i → (G.cutE (A.specOf G)).AncAvoid D w i := by
  intro w hpath
  unfold ADMG.AncAvoid Reach at hpath
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ => Reach.refl i
  | @head a b hab hbi ih =>
    intro ha
    obtain ⟨hab1, hbD⟩ := hab
    have hbsub : b ∉ A.sub i := fun hb => hbD (hD hb)
    have hbi' : G.AncAvoid D b i := hbi
    have hbcomp : b ∈ A.comp G i :=
      Scb2018.mem_diagH.mpr ⟨hbsub, Reach.mono_avoid hD hbi'⟩
    have habS : (a, b) ∉ A.specOf G := by
      intro habS
      obtain ⟨j, hj, haj, -, hbj⟩ := mem_specOf.mp habS
      have hmem : a ∈ A.msub G j b := mem_msub_of_dir haj hab1 hbj
      rw [h j hj i hi b hbj hbcomp] at hmem
      exact ha (msub_subset hmem)
    exact Reach.head (ADMG.cutE_dir.mpr ⟨hab1, habS⟩) hbD (ih hbsub)

/-! ### Specification and realizability -/

/-- Every selected input of `specOf G A` is required by some target (it enters the target's
computation along a path of `𝒢_{specOf G A}`), when the targets' computations use the same
minimized subscript variables. -/
theorem reqEdges_specOf (h : A.SameVars G) : reqEdges G A.tgt (A.specOf G) = A.specOf G := by
  apply Finset.ext
  rintro ⟨p, v⟩
  rw [mem_reqEdges]
  constructor
  · exact fun h' => h'.1
  · intro hpv
    obtain ⟨i, hi, -, hd, hvi⟩ := mem_specOf.mp hpv
    have hvi' := Scb2018.mem_diagH.mp hvi
    exact ⟨hpv, hd, i, hi, (G.cutE (A.specOf G)).anc_of_avoid
      (ancAvoid_cutE_specOf h hi (Finset.Subset.refl _) v hvi'.2 hvi'.1)⟩

/-- The literal test of  on `An(Y_𝐱, 𝐗_∗)` (the ICLR's Prop. 1 criterion) implies
realizability. -/
theorem realizable_of_noConflict (hstd : A.Std y) {Ω : Fin n → Type} {c : Fin n → ∀ j, Ω j}
    (h : A.NoConflict G y c) : A.Realizable G y c := by
  refine ⟨h.1, ?_⟩
  intro v hv hvy _ p hp
  cases hpv : G.dir p v with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨i, hi, hpi, -, hvi⟩ := mem_specOf.mp hp
    have h2 := (h.2 i hi v hv hvy hvi).2
    have hmem : p ∈ A.msub G i v := mem_msub_of_dir hpi hpv hvi
    rw [h2] at hmem
    exact Finset.notMem_empty p hmem

section Bridge

variable {Ω : Fin n → Type} {L : Type} {U : L → Type} [DecidableEq L] [∀ i, Inhabited (Ω i)]
  {M : Mech n Ω L U}

/-- Under `Consistent`, the value that `specVal` gives to a selected input `(p, v)` is the value of
`p` in the subscript of any target whose computation selects it. -/
theorem specVal_eq {c : Fin n → ∀ j, Ω j} (h : A.Consistent G c) {i : Fin n} (hi : i ∈ A.tgt)
    {p v : Fin n} (hp : p ∈ A.sub i) (hpv : G.dir p v = true) (hv : v ∈ A.comp G i) :
    A.specVal G c v p = c i p := by
  have hex : ∃ i' ∈ A.tgt, p ∈ A.sub i' ∧ G.dir p v = true ∧ v ∈ A.comp G i' :=
    ⟨i, hi, hp, hpv, hv⟩
  have hs : A.specVal G c v p = c (Classical.choose hex) p := dite_eq_left hex
  rw [hs]
  obtain ⟨hi', hp', -, hv'⟩ := Classical.choose_spec hex
  exact h.2 _ hi' i hi v hv' hv p (mem_msub_of_dir hp' hpv hv')

/-- The counterfactual `X_{i[𝐰_i]}(𝐮)` of a target is its value in the world of `specOf G A`
when the targets' computations are consistent. -/
theorem target_eq_respE (hstd : A.Std y) (hM : M.diag = G) {c : Fin n → ∀ j, Ω j}
    (h : A.Consistent G c) (u : ∀ l, U l) {i : Fin n} (hi : i ∈ A.tgt) :
    M.resp (A.sub i) (c i) u i = M.respE (A.specOf G) (A.specVal G c) u i := by
  -- Rank induction over the computation of `X_i`: an input from `𝐖_i` is selected with the
  -- value `c i`, every other input comes from the computation and is not selected.
  have key : ∀ v, v ∈ A.comp G i →
      M.resp (A.sub i) (c i) u v = M.respE (A.specOf G) (A.specVal G c) u v := by
    intro v
    refine rank_induction M.rank (P := fun v => v ∈ A.comp G i →
      M.resp (A.sub i) (c i) u v = M.respE (A.specOf G) (A.specVal G c) u v)
      (fun v ih hv => ?_) v
    have hv' := Scb2018.mem_diagH.mp hv
    rw [M.resp_of_not_mem hv'.1, M.respE_spec (A.specOf G) (A.specVal G c) u v]
    apply M.f_pa
    intro j hj
    have hjv : G.dir j v = true := (mem_pa_iff_of_diag_eq hM).mp hj
    show M.resp (A.sub i) (c i) u j =
      (if (j, v) ∈ A.specOf G then A.specVal G c v j
        else M.respE (A.specOf G) (A.specVal G c) u j)
    by_cases hji : j ∈ A.sub i
    · have hjS : (j, v) ∈ A.specOf G := mem_specOf.mpr ⟨i, hi, hji, hjv, hv⟩
      rw [ite_eq_left hjS, M.resp_of_mem hji]
      exact (specVal_eq h hi hji hjv hv).symm
    · have hjS : (j, v) ∉ A.specOf G := by
        intro hjS
        obtain ⟨i', hi', hji', -, hvi'⟩ := mem_specOf.mp hjS
        have hmem : j ∈ A.msub G i' v := mem_msub_of_dir hji' hjv hvi'
        rw [← h.1 i hi i' hi' v hv hvi'] at hmem
        exact hji (msub_subset hmem)
      rw [ite_eq_right hjS]
      exact ih j (M.pa_rank hj) (Scb2018.mem_diagH.mpr ⟨hji, Reach.head hjv hv'.1 hv'.2⟩)
  exact key i (Scb2018.mem_diagH.mpr ⟨hstd.2 i hi, Reach.refl i⟩)

/-- The nested reward of a consistent unnested action is the reward of the outer-target action
`(𝐗, specOf G A)` on every unit. -/
theorem reward_eq_outer (hstd : A.Std y) (hM : M.diag = G) {c : Fin n → ∀ j, Ω j}
    (h : A.Consistent G c) (u : ∀ l, U l) :
    A.reward M c u y = M.resp A.tgt (M.respE (A.specOf G) (A.specVal G c) u) u y := by
  have hx : ∀ i ∈ A.tgt, M.resp (A.sub i) (c i) u i =
      M.respE (A.specOf G) (A.specVal G c) u i :=
    fun i hi => target_eq_respE hstd hM h u hi
  show M.resp A.tgt (fun i => M.resp (A.sub i) (c i) u i) u y = _
  exact congrFun (M.resp_congr u hx) y

/-- **`prop: cover realizable nested counterfactuals`** for unnested actions:
a realizable unnested action is implemented by its parent-input specification, with the same
reward on every unit. -/
theorem reward_eq_spec (hstd : A.Std y) (hM : M.diag = G) {c : Fin n → ∀ j, Ω j}
    (h : A.Realizable G y c) (u : ∀ l, U l) :
    A.reward M c u y = M.respE (A.specOf G) (A.specVal G c) u y := by
  rw [reward_eq_outer hstd hM h.1 u, resp_eq_respE_reqEdges hM h.2, reqEdges_specOf h.1.1]

end Bridge

/-- **`cor: ctfmis for unnested counterfactual`**: for a realizable unnested
set satisfying condition 1, condition 2 for the target `x` is equivalent to
`𝐖_x ∩ An(x)_{𝒢_{\overline{𝐗 ∖ \{x\}}}} ≠ ∅`.  The graph `𝒢_{𝐗_∗}` is `𝒢_{specOf G A}`.

The hypothesis `h1` (condition 1) is the corollary's; the proof does not need it. -/
theorem cond2_iff (hstd : A.Std y) {Ω : Fin n → Type} {c : Fin n → ∀ j, Ω j}
    (hR : A.Realizable G y c) (h1 : AncCrit G y A.tgt) {x : Fin n} (hx : x ∈ A.tgt) :
    Cond2 G A.tgt (A.specOf G) x ↔ ∃ w ∈ A.sub x, G.AncAvoid (A.tgt.erase x) w x := by
  have hsv : A.SameVars G := hR.1.1
  have hxx : x ∉ A.sub x := hstd.2 x hx
  -- No directed path of `𝒢_{𝐗_∗}` leaves `𝐖_x` and reaches `x` avoiding `𝐖_x`: its first edge
  -- enters the computation of `X_x` from `𝐖_x`, so it is selected.
  have hno : ∀ a ∈ A.sub x,
      ¬ Reach (G.cutE (A.specOf G)).dir (A.tgt.erase x ∪ A.sub x) a x := by
    intro a ha hreach
    rcases Relation.ReflTransGen.cases_head hreach with hax | ⟨b, hab, hbx⟩
    · rw [hax] at ha
      exact hxx ha
    · obtain ⟨hab1, hbD⟩ := hab
      obtain ⟨hdir, habS⟩ := ADMG.cutE_dir.mp hab1
      have hbx' : (G.cutE (A.specOf G)).AncAvoid (A.tgt.erase x ∪ A.sub x) b x := hbx
      have hbsub : b ∉ A.sub x := fun hb => hbD (Finset.mem_union_right _ hb)
      have hbcomp : b ∈ A.comp G x := Scb2018.mem_diagH.mpr
        ⟨hbsub, Reach.mono_avoid Finset.subset_union_right (ancAvoid_of_ancAvoid_cutE hbx')⟩
      exact habS (mem_specOf.mpr ⟨x, hx, ha, hdir, hbcomp⟩)
  constructor
  · -- The path of condition 2 lies in the computation of `X_x`; the selected input entering its
    -- first vertex comes from the minimized subscript there, which `SameVars` places in `𝐖_x`.
    rintro ⟨p, v, hpv, hd, hv, hpath⟩
    obtain ⟨j, hj, hpj, -, hvj⟩ := mem_specOf.mp hpv
    rcases Reach.split_last (A.sub x) hpath with hp' | ⟨a, ha, -, ha'⟩
    · have hvx : v ∉ A.sub x := fun hvs => hno v hvs hp'
      have hp'' : (G.cutE (A.specOf G)).AncAvoid (A.tgt.erase x ∪ A.sub x) v x := hp'
      have hvcomp : v ∈ A.comp G x := Scb2018.mem_diagH.mpr
        ⟨hvx, Reach.mono_avoid Finset.subset_union_right (ancAvoid_of_ancAvoid_cutE hp'')⟩
      have hpm : p ∈ A.msub G j v := mem_msub_of_dir hpj hd hvj
      rw [hsv j hj x hx v hvj hvcomp] at hpm
      exact ⟨p, msub_subset hpm, Reach.head hd hv (ancAvoid_of_ancAvoid_cutE hpath)⟩
    · exact absurd ha' (hno a ha)
  · -- From the last vertex of `𝐖_x` on the path, the next edge is selected by the computation of
    -- `X_x`, and the rest of the path is a path of `𝒢_{𝐗_∗}`.
    rintro ⟨w, hw, hpath⟩
    obtain ⟨a, ha, hax⟩ : ∃ a ∈ A.sub x, Reach G.dir (A.tgt.erase x ∪ A.sub x) a x := by
      rcases Reach.split_last (A.sub x) hpath with hp' | ⟨a, ha, -, ha'⟩
      · exact ⟨w, hw, hp'⟩
      · exact ⟨a, ha, ha'⟩
    rcases Relation.ReflTransGen.cases_head hax with hax' | ⟨b, hab, hbx⟩
    · rw [hax'] at ha
      exact absurd ha hxx
    · obtain ⟨hab1, hbD⟩ := hab
      have hbx' : G.AncAvoid (A.tgt.erase x ∪ A.sub x) b x := hbx
      have hbsub : b ∉ A.sub x := fun hb => hbD (Finset.mem_union_right _ hb)
      have hbcomp : b ∈ A.comp G x :=
        Scb2018.mem_diagH.mpr ⟨hbsub, Reach.mono_avoid Finset.subset_union_right hbx'⟩
      exact ⟨a, b, mem_specOf.mpr ⟨x, hx, ha, hab1, hbcomp⟩, hab1,
        fun hb => hbD (Finset.mem_union_left _ hb),
        Reach.mono_avoid Finset.subset_union_left
          (ancAvoid_cutE_specOf hsv hx Finset.subset_union_right b hbx' hbsub)⟩

/-- `thm: ctf-mis` with `cor: ctfmis for unnested counterfactual`: for a realizable unnested set,
the outer-target action `(𝐗, specOf G A)` is a ctf-MIS iff (i) `𝐗 ⊆ An(Y)_{𝒢_{\overline 𝐗}}` and
(ii) `𝐖_i ∩ An(X_i)_{𝒢_{\overline{𝐗 ∖ \{X_i\}}}} ≠ ∅` for every target: the statement of the
ICLR's Thm. 1. -/
theorem ctfMIS_iff_unnested (hG : G.WF) (hstd : A.Std y) {Ω : Fin n → Type}
    {c : Fin n → ∀ j, Ω j} (hR : A.Realizable G y c) :
    CtfMIS G y A.tgt (A.specOf G) ↔
      AncCrit G y A.tgt ∧ ∀ x ∈ A.tgt, ∃ w ∈ A.sub x, G.AncAvoid (A.tgt.erase x) w x := by
  rw [ctfMIS_iff hG hstd.1]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x hx => (cond2_iff hstd hR h1 hx).mp (h2 x hx)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x hx => (cond2_iff hstd hR h1 hx).mpr (h2 x hx)⟩

end UCtf

end Mec.CtfScb

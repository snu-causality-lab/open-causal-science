import MecLean.CtfScb.Defs

set_option linter.unusedSectionVars false

/-!
# Minimal counterfactual interventions

Direct evaluation of finite structural equations gives ordinary-intervention dominance and
the characterization of minimal counterfactual outer-target actions. The unnested
specialization is in `MecLean.CtfScb.Unnested`.
-/

open Finset

namespace Mec.CtfScb

open Mec Mec.ScbMec

variable {n : ℕ}

/-! ## `cor: l2 dominance` -/

/-- The ordinary intervention `do(S = x)` with `Y ∉ S` is the specification that fixes every
outgoing input of `S` in the model's diagram to the value of its source (proof of
`cor: l2 dominance`). -/
theorem mu_eq_muE_outE (m : Model n) {y : Fin n} (r : m.X y → ℝ) {S : Finset (Fin n)}
    (hy : y ∉ S) (x : ∀ i, m.X i) :
    m.mu y r S x = m.muE y r (m.scm.toMech.diag.outE S) (fun _ j => x j) := by
  unfold Model.mu Model.muE
  exact m.scm.E_congr (fun u => congrArg r (Mech.resp_eq_respE S x u hy))

/-- The best ordinary intervention on `S` is matched by the specification `outE S` with its
values chosen freely. -/
theorem best_le_bestE_outE (m : Model n) {y : Fin n} (r : m.X y → ℝ) {S : Finset (Fin n)}
    (hy : y ∉ S) : m.best y r S ≤ m.bestE y r (m.scm.toMech.diag.outE S) := by
  obtain ⟨x, hx⟩ := m.exists_best y r S
  rw [← hx, mu_eq_muE_outE m r hy x]
  exact m.muE_le_bestE y r _ _

/-- **`cor: l2 dominance`**: the optimal ordinary
intervention cannot outperform the optimal counterfactual action, `μ_{𝐱^⋆} ≤ μ_{𝐗_{∗∗}^⋆}`.
It holds in every model; the diagram enters only through `mu_eq_muE_outE`. -/
theorem l2_dominance (m : Model n) (y : Fin n) (r : m.X y → ℝ) : ordOpt m y r ≤ ctfOpt m y r := by
  unfold ordOpt
  refine Finset.sup'_le _ _ (fun S hS => ?_)
  have hy : y ∉ S := (Finset.mem_filter.mp hS).2
  refine le_trans (best_le_bestE_outE m r hy) ?_
  unfold ctfOpt
  exact Finset.le_sup' (fun F => m.bestE y r F) (Finset.mem_univ _)

/-! ## The two deletions of `thm: ctf-mis`, "only if" -/

section Pointwise

variable {G : ADMG n} {Ω : Fin n → Type} {L : Type} {U : L → Type} [DecidableEq L]
  [∀ i, Inhabited (Ω i)] {M : Mech n Ω L U}

/-- **Failure of condition 1** (`thm: ctf-mis`, "only if"): if `x ∈ X` has no
directed path to `y` avoiding the other targets, deleting the outer assignment to `x` preserves the
reward on every unit; the inner computations of the other targets are unchanged. -/
theorem resp_erase_of_not_cond1 (hM : M.diag = G) {X : Finset (Fin n)} {x y : Fin n}
    (hx : x ∈ X) (h : ¬ G.AncAvoid X x y) (F : EdgeSet n) (c : Fin n → ∀ p, Ω p)
    (u : ∀ l, U l) :
    M.resp (X.erase x) (M.respE F c u) u y = M.resp X (M.respE F c u) u y := by
  have hG : G.WF := by
    rw [← hM]
    exact M.diag_wf
  symm
  apply Mech.resp_restrict (Finset.erase_subset x X)
  intro d hdX hdT hpath
  have hdx : d = x := by
    by_contra hne
    exact hdT (Finset.mem_erase.mpr ⟨hne, hdX⟩)
  rw [hdx, hM] at hpath
  exact h (ScbMec.ancAvoid_of_erase hG hpath)

/-- **Failure of condition 2** (`thm: ctf-mis`, "only if"): if no vertex with a
directed path of `𝒢_F` to `x` avoiding the other targets receives a constant, the outer system of
`X ∖ {x}` computes `x` as the world of `F` does, so deleting the outer assignment to `x` preserves
the reward on every unit.  The corresponding statement also assumes condition 1 here; the identity does not
need it. -/
theorem resp_erase_of_not_cond2 (hM : M.diag = G) {X : Finset (Fin n)} {x : Fin n}
    {F : EdgeSet n} (hx : x ∈ X) (h : ¬ Cond2 G X F x) (c : Fin n → ∀ p, Ω p) (u : ∀ l, U l)
    (y : Fin n) :
    M.resp (X.erase x) (M.respE F c u) u y = M.resp X (M.respE F c u) u y := by
  -- A vertex outside `X ∖ {x}` with a path of `𝒢_F` to `x` avoiding `X ∖ {x}` receives no
  -- constant (failure of condition 2), so the outer system of `X ∖ {x}` computes it as the world
  -- of `F` does (rank induction; the remaining targets supply their values in that world).
  have key : ∀ w, w ∉ X.erase x → (G.cutE F).AncAvoid (X.erase x) w x →
      M.resp (X.erase x) (M.respE F c u) u w = M.respE F c u w := by
    intro w
    refine rank_induction M.rank (P := fun w => w ∉ X.erase x →
      (G.cutE F).AncAvoid (X.erase x) w x →
      M.resp (X.erase x) (M.respE F c u) u w = M.respE F c u w) (fun w ih hw hpath => ?_) w
    rw [Mech.resp_of_not_mem hw, M.respE_spec F c u w]
    apply M.f_pa
    intro j hj
    have hdir : G.dir j w = true := by
      rw [← hM]
      exact (M.diag_dir).mpr hj
    have hjF : (j, w) ∉ F := fun hjF => h ⟨j, w, hjF, hdir, hw, hpath⟩
    show M.resp (X.erase x) (M.respE F c u) u j =
      (if (j, w) ∈ F then c w j else M.respE F c u j)
    rw [if_neg hjF]
    by_cases hjT : j ∈ X.erase x
    · exact Mech.resp_of_mem hjT
    · refine ih j (M.pa_rank hj) hjT ?_
      have hedge : (G.cutE F).dir j w = true := ADMG.cutE_dir.mpr ⟨hdir, hjF⟩
      exact Reach.head hedge hw hpath
  -- Composition: the outer system of `X` fixes `x` at the value just computed.
  have hxT : x ∉ X.erase x := fun hmem => (Finset.mem_erase.mp hmem).1 rfl
  have hext : M.resp X (M.respE F c u) u = M.resp (X.erase x) (M.respE F c u) u := by
    refine Mech.resp_extend (Finset.erase_subset x X) (M.respE F c u) (M.respE F c u) u
      (fun _ _ => rfl) (fun i hiX hiT => ?_)
    have hix : i = x := by
      by_contra hne
      exact hiT (Finset.mem_erase.mpr ⟨hne, hiX⟩)
    rw [hix]
    exact (key x hxT (Reach.refl x)).symm
  rw [hext]

end Pointwise

/-! ## `thm: ctf-mis` -/

/-- A target that satisfies condition 2 keeps it when other targets are deleted: the witnessing
path remains available. -/
theorem Cond2.mono {G : ADMG n} {X X' : Finset (Fin n)} {F : EdgeSet n} {x : Fin n}
    (hX : X' ⊆ X) (h : Cond2 G X F x) : Cond2 G X' F x := by
  obtain ⟨p, v, hF, hd, hv, hpath⟩ := h
  have hsub : X'.erase x ⊆ X.erase x := Finset.erase_subset_erase x hX
  exact ⟨p, v, hF, hd, fun h' => hv (hsub h'), Reach.mono_avoid hsub hpath⟩

/-! ### The Boolean witness for the "if" part

For a proper subset `Z ⊊ X`, the witness is deterministic and Boolean on the causal diagram `𝒢`:
a vertex of `Z` is constant `false`, every other vertex is the OR of its parents in `𝒢`, and every
selected input receives `true`.  In the world of `F` a target `x ∉ Z` is `true` (condition 2), so
`y` is `true` in the outer system of `X` (condition 1).  In the outer system of `Z` every vertex is
`false`: the targets of `Z` keep their values in the world of `F`, which are `false`, and no
constant enters the outer system. -/

namespace MISWitness

/-- The mechanism of vertex `i`: `false` on `Z`, otherwise the OR of the parents in `G`. -/
def orZ (G : ADMG n) (Z : Finset (Fin n)) (i : Fin n) (z : Fin n → Bool)
    (_u : Roots n → Unit) : Bool :=
  decide (i ∉ Z ∧ ∃ j, G.dir j i = true ∧ z j = true)

theorem orZ_pa (G : ADMG n) (Z : Finset (Fin n)) (i : Fin n) (z z' : Fin n → Bool)
    (u : Roots n → Unit) (h : ∀ j, G.dir j i = true → z j = z' j) :
    orZ G Z i z u = orZ G Z i z' u := by
  unfold orZ
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_iff]
  exact and_congr_right (fun _ =>
    exists_congr (fun j => and_congr_right (fun hj => by rw [h j hj])))

/-- The witness mechanisms; their causal diagram is `G`. -/
def mech (G : ADMG n) (hG : G.WF) (Z : Finset (Fin n)) :
    Mech n (fun _ => Bool) (Roots n) (fun _ => Unit) :=
  Mech.ofADMG G hG (orZ G Z) (orZ_pa G Z) (fun _ _ _ _ _ => rfl)

theorem mech_diag (G : ADMG n) (hG : G.WF) (Z : Finset (Fin n)) : (mech G hG Z).diag = G := by
  unfold mech
  exact Mech.ofADMG_diag G hG _ _ _

theorem mech_f (G : ADMG n) (hG : G.WF) (Z : Finset (Fin n)) (i : Fin n) (z : Fin n → Bool)
    (u : Roots n → Unit) :
    (mech G hG Z).f i z u = decide (i ∉ Z ∧ ∃ j, G.dir j i = true ∧ z j = true) := rfl

/-- In the world of `F` with every selected input `true`, a vertex outside `Z` receiving a selected
input of `𝒢` is `true`, and so is every vertex it reaches in `𝒢_F` avoiding `Z`. -/
theorem respE_true {G : ADMG n} (hG : G.WF) {Z : Finset (Fin n)} {F : EdgeSet n}
    {p v w : Fin n} (hpv : (p, v) ∈ F) (hdir : G.dir p v = true) (hv : v ∉ Z)
    (hpath : (G.cutE F).AncAvoid Z v w) (u : Roots n → Unit) :
    (mech G hG Z).respE F (fun _ _ => true) u w = true := by
  unfold ADMG.AncAvoid at hpath
  induction hpath with
  | refl =>
    rw [Mech.respE_spec, mech_f]
    refine decide_eq_true ⟨hv, p, hdir, ?_⟩
    rw [if_pos hpv]
  | @tail b d _ hbd ih =>
    rw [Mech.respE_spec, mech_f]
    have hb : G.dir b d = true ∧ (b, d) ∉ F := ADMG.cutE_dir.mp hbd.1
    refine decide_eq_true ⟨hbd.2, b, hb.1, ?_⟩
    rw [if_neg hb.2]
    exact ih

/-- In every world, a vertex of `Z` is `false`. -/
theorem respE_false {G : ADMG n} (hG : G.WF) {Z : Finset (Fin n)} (F : EdgeSet n)
    (c : Fin n → Fin n → Bool) {i : Fin n} (hi : i ∈ Z) (u : Roots n → Unit) :
    (mech G hG Z).respE F c u i = false := by
  rw [Mech.respE_spec, mech_f]
  exact decide_eq_false (by rintro ⟨hiZ, -⟩; exact hiZ hi)

/-- Under `do(S = z)` with `Z ⊆ S` and `z x = true` for `x ∈ S`, every vertex reached from `x` by a
directed path avoiding `S` is `true`. -/
theorem resp_true {G : ADMG n} (hG : G.WF) {Z S : Finset (Fin n)} (hZS : Z ⊆ S)
    {z : Fin n → Bool} {x w : Fin n} (hxS : x ∈ S) (hzx : z x = true)
    (hpath : G.AncAvoid S x w) (u : Roots n → Unit) :
    (mech G hG Z).resp S z u w = true := by
  unfold ADMG.AncAvoid at hpath
  induction hpath with
  | refl =>
    rw [Mech.resp_of_mem hxS]
    exact hzx
  | @tail b d _ hbd ih =>
    rw [Mech.resp_of_not_mem hbd.2, mech_f]
    exact decide_eq_true ⟨fun hdZ => hbd.2 (hZS hdZ), b, hbd.1, ih⟩

/-- Under `do(Z = z)` with `z` false on `Z`, every vertex is `false`. -/
theorem resp_false {G : ADMG n} (hG : G.WF) {Z : Finset (Fin n)} {z : Fin n → Bool}
    (hz : ∀ i ∈ Z, z i = false) (u : Roots n → Unit) (w : Fin n) :
    (mech G hG Z).resp Z z u w = false := by
  have h : (fun _ : Fin n => false) = (mech G hG Z).resp Z z u := by
    apply Mech.eq_resp
    intro i
    by_cases hi : i ∈ Z
    · rw [if_pos hi, hz i hi]
    · rw [if_neg hi, mech_f]
      simp
  rw [← h]

/-- The reward of an outer-target action in a deterministic model is its value at the unique
exogenous point. -/
theorem ofDet_muSet {Ω : Fin n → Type} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    [∀ i, Inhabited (Ω i)] (M : Mech n Ω (Roots n) (fun _ => Unit)) (y : Fin n) (r : Ω y → ℝ)
    (S : Finset (Fin n)) (F : EdgeSet n) (c : Fin n → ∀ p, Ω p) :
    (Model.ofDet M).muSet y r S F c =
      r (M.resp S (M.respE F c (fun _ : Roots n => ())) (fun _ : Roots n => ()) y) := by
  have hs : Subsingleton (∀ l : Roots n, Unit) := ⟨fun a b => funext (fun _ => rfl)⟩
  unfold Model.muSet
  exact SCM.E_of_subsingleton (Model.ofDet M).scm (hsub := hs) _ (fun _ : Roots n => ())

end MISWitness

/-- **`thm: ctf-mis`**: the
outer-target action `(X, F)` is a ctf-MIS iff (1) `𝐗 ⊆ An(Y)_{𝒢_{\overline 𝐗}}` and (2) every
target satisfies `Cond2`.

Deviation: the assumptions of realizability and nonconstant terms are dropped; in the
outer-target form every target is computed by its mechanism in one world.
The "if" part may use any witness; the binary threshold SCM of  has non-finite
exogenous variables, and a deterministic Boolean witness suffices. -/
theorem ctfMIS_iff {G : ADMG n} (hG : G.WF) {y : Fin n} {X : Finset (Fin n)} {F : EdgeSet n}
    (hy : y ∉ X) : CtfMIS G y X F ↔ AncCrit G y X ∧ ∀ x ∈ X, Cond2 G X F x := by
  constructor
  · -- "only if": a target failing either condition can be deleted without changing the reward
    -- on any unit, in every model conforming to `𝒢`
    rintro ⟨-, hsep⟩
    have hdel : ∀ x ∈ X, (¬ G.AncAvoid X x y ∨ ¬ Cond2 G X F x) → False := by
      intro x hx hfail
      obtain ⟨m, r, c, hm, hne⟩ := hsep (X.erase x) (Finset.erase_ssubset hx)
      have hM : m.scm.toMech.diag = G := hm
      apply hne
      unfold Model.muSet
      refine m.scm.E_congr (fun u => ?_)
      rcases hfail with h1 | h2
      · exact congrArg r (resp_erase_of_not_cond1 hM hx h1 F c u)
      · exact congrArg r (resp_erase_of_not_cond2 hM hx h2 c u y)
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · by_contra h1
      exact hdel x hx (Or.inl h1)
    · by_contra h2
      exact hdel x hx (Or.inr h2)
  · -- "if": for each proper subset `Z`, the Boolean witness of `MISWitness`
    rintro ⟨h1, h2⟩
    refine ⟨hy, fun Z hZ => ?_⟩
    obtain ⟨x, hxX, hxZ⟩ := Finset.exists_of_ssubset hZ
    have hZX : Z ⊆ X := (Finset.ssubset_def.mp hZ).1
    have hZT : Z ⊆ X.erase x := fun i hi =>
      Finset.mem_erase.mpr ⟨fun hix => hxZ (by rw [← hix]; exact hi), hZX hi⟩
    obtain ⟨p, v, hpv, hdir, hv, hpath⟩ := h2 x hxX
    have hx1 : (MISWitness.mech G hG Z).respE F (fun _ _ => true) (fun _ => ()) x = true :=
      MISWitness.respE_true hG hpv hdir (fun hvZ => hv (hZT hvZ)) (Reach.mono_avoid hZT hpath) _
    have hfalse : ∀ i ∈ Z,
        (MISWitness.mech G hG Z).respE F (fun _ _ => true) (fun _ => ()) i = false :=
      fun i hi => MISWitness.respE_false hG F _ hi _
    refine ⟨Model.ofDet (MISWitness.mech G hG Z), fun b : Bool => if b then 1 else 0,
      fun _ _ => true, MISWitness.mech_diag G hG Z, ?_⟩
    rw [MISWitness.ofDet_muSet, MISWitness.ofDet_muSet, MISWitness.resp_false hG hfalse,
      MISWitness.resp_true hG hZX hxX hx1 (h1 x hxX)]
    simp

end Mec.CtfScb

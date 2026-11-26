import MecLean.Common.Indep
import OpenCausalScienceAnalysis.Identification.QFactorGraph

/-!
# Causal factors in a finite SCM

Tian and Pearl, *On the Identification of Causal Effects*, R-290-L (2003), Lemmas 3 and 4.
The SCM has finite state spaces and independent exogenous roots. A root may enter more
than one equation. The causal diagram records the corresponding bidirected edges.

`SCM.Q_marg_ancestral` proves Eq. (69) and `SCM.Q_prod_ccomps` proves Eq. (70). The prefix
ratio formula in Eq. (71) is verified by `SCM.cfac_eq_Q` where its denominators are
positive. Zero-valued factors are allowed in the marginalization and product identities.

Source: https://ftp.cs.ucla.edu/pub/stat_ser/R290-L.pdf#page=22
-/

open Finset

namespace Mec

variable {n : ℕ}

/-! ## Finite marginal sums -/

section Assign

variable {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-- The assignments that agree with `v` outside `A`: the values of `A` vary, every other argument
stays fixed at `v`. -/
def varyOn (A : Finset (Fin n)) (v : ∀ i, X i) : Finset (∀ i, X i) :=
  Finset.univ.filter (fun w => ∀ i, i ∉ A → w i = v i)

/-- `∑_a g`: the sum of `g` over the values of `A`, every other argument fixed at `v`. -/
noncomputable def margSum (A : Finset (Fin n)) (v : ∀ i, X i) (g : (∀ i, X i) → ℝ) : ℝ :=
  ∑ w ∈ varyOn A v, g w

end Assign

/-- The values of `w` on `A` and of `v` elsewhere. -/
def patch {X : Fin n → Type} (A : Finset (Fin n)) (w v : ∀ i, X i) : ∀ i, X i :=
  fun i => if i ∈ A then w i else v i

namespace QFac

section Tools

variable {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

theorem mem_varyOn {A : Finset (Fin n)} {v w : ∀ i, X i} :
    w ∈ varyOn A v ↔ ∀ i, i ∉ A → w i = v i := by
  simp [varyOn]

theorem patch_mem_varyOn (A : Finset (Fin n)) (g v : ∀ i, X i) : patch A g v ∈ varyOn A v :=
  mem_varyOn.mpr (fun i hi => by simp [patch, hi])

/-- Exactly one assignment of `varyOn A v` agrees with `g` on `A`. -/
theorem sum_varyOn_ite (A : Finset (Fin n)) (v g : ∀ i, X i) (φ : (∀ i, X i) → ℝ) :
    ∑ w ∈ varyOn A v, (if ∀ i ∈ A, g i = w i then φ w else 0) = φ (patch A g v) := by
  rw [Finset.sum_eq_single (patch A g v)]
  · exact ite_eq_left (fun i hi => by simp [patch, hi])
  · intro w hw hne
    refine ite_eq_right (fun h => hne ?_)
    funext i
    show w i = if i ∈ A then g i else v i
    by_cases hi : i ∈ A
    · rw [ite_eq_left hi]
      exact (h i hi).symm
    · rw [ite_eq_right hi]
      exact mem_varyOn.mp hw i hi
  · intro hnot
    exact absurd (patch_mem_varyOn A g v) hnot

end Tools

end QFac

/-! ## The district factor formula -/

section CFactor

variable {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-- The marginal of a factor over the first `k` vertices of `ord`. Coordinates outside
`H` are fixed at `v`. -/
noncomputable def prefixMarg (ord : List (Fin n)) (H : Finset (Fin n))
    (P : (∀ i, X i) → ℝ) (k : ℕ) (v : ∀ i, X i) : ℝ :=
  margSum (H \ (ord.take k).toFinset) v P

/-- Tian and Pearl's district factor extraction by ratios of successive prefix marginals.
The correctness theorem assumes the selected denominators are positive. -/
noncomputable def cfac (ord : List (Fin n)) (H C : Finset (Fin n))
    (P : (∀ i, X i) → ℝ) (v : ∀ i, X i) : ℝ :=
  ∏ c ∈ C,
    prefixMarg ord H P (ord.idxOf c + 1) v / prefixMarg ord H P (ord.idxOf c) v

end CFactor

/-! ## Interventional probabilities and causal factors -/

open QFac

namespace SCM

variable {X : Fin n → Type} {L : Type} {U : L → Type} [Fintype L] [DecidableEq L]
  [∀ l, Fintype (U l)] [∀ i, Fintype (X i)] [∀ i, Inhabited (X i)] [∀ i, DecidableEq (X i)]
  (M : SCM n X L U)

/-- `P_x(A = a)`: the probability under `do(S = x)` that every vertex of `A` takes its value in
`a` (only the values of `x` on `S` and of `a` on `A` matter). -/
noncomputable def Pdo (S : Finset (Fin n)) (x : ∀ i, X i) (A : Finset (Fin n))
    (a : ∀ i, X i) : ℝ :=
  M.P (fun u => ∀ i ∈ A, M.toMech.resp S x u i = a i)

/-- The causal factor `Q[C](v) = P_{v \ C}(c)`: the
probability that `C` takes its values in `v` when every vertex outside `C` is fixed at `v`. -/
noncomputable def Q (C : Finset (Fin n)) (v : ∀ i, X i) : ℝ :=
  M.Pdo (univ \ C) v C v

section EventProbability

omit [∀ i, Fintype (X i)] [∀ i, Inhabited (X i)] [∀ i, DecidableEq (X i)]

theorem P_eq_E (E : (∀ l, U l) → Prop) [DecidablePred E] :
    M.P E = M.E (fun u => if E u then 1 else 0) := by
  unfold SCM.P SCM.E
  refine Finset.sum_congr rfl (fun u _ => ?_)
  by_cases h : E u <;> simp [h]

theorem P_true : M.P (fun _ => True) = 1 := by
  unfold SCM.P
  simp [M.sum_prob]

/-- `P` does not depend on the decidability instance of the event. -/
theorem P_congr_inst {E₁ E₂ : (∀ l, U l) → Prop} (i₁ : DecidablePred E₁)
    (i₂ : DecidablePred E₂) (h : ∀ u, E₁ u ↔ E₂ u) :
    @SCM.P n X L U _ _ _ M E₁ i₁ = @SCM.P n X L U _ _ _ M E₂ i₂ := by
  have hE : E₁ = E₂ := funext (fun u => propext (h u))
  subst hE
  obtain rfl := Subsingleton.elim i₁ i₂
  rfl

end EventProbability

omit [∀ i, Fintype (X i)] in
theorem Q_nonneg (C : Finset (Fin n)) (v : ∀ i, X i) : 0 ≤ M.Q C v :=
  M.P_nonneg _

omit [∀ i, Inhabited (X i)] in
/-- Summing a weight against the events "the response agrees with `w` on `A`", over the
assignments `w` of `A`, is an expectation. -/
theorem sum_varyOn_mul_P (A : Finset (Fin n)) (v : ∀ i, X i) (φ : (∀ i, X i) → ℝ)
    (E : (∀ l, U l) → Prop) [DecidablePred E] (g : (∀ l, U l) → ∀ i, X i) :
    ∑ w ∈ varyOn A v, φ w * M.P (fun u => E u ∧ ∀ i ∈ A, g u i = w i) =
      M.E (fun u => if E u then φ (patch A (g u) v) else 0) := by
  unfold SCM.P SCM.E
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  by_cases hE : E u
  · have h : ∀ w, φ w * (if E u ∧ ∀ i ∈ A, g u i = w i then M.prob u else 0) =
        M.prob u * (if ∀ i ∈ A, g u i = w i then φ w else 0) := by
      intro w
      by_cases hw : ∀ i ∈ A, g u i = w i
      · rw [ite_eq_left ⟨hE, hw⟩, ite_eq_left hw, mul_comm]
      · rw [ite_eq_right (fun h => hw h.2), ite_eq_right hw, mul_zero, mul_zero]
    simp_rw [h]
    rw [← Finset.mul_sum, sum_varyOn_ite, ite_eq_left hE]
  · have h : ∀ w, φ w * (if E u ∧ ∀ i ∈ A, g u i = w i then M.prob u else 0) = 0 := by
      intro w
      rw [ite_eq_right (fun h => hE h.1), mul_zero]
    simp_rw [h]
    rw [Finset.sum_const_zero, ite_eq_right hE, mul_zero]

/-- A weighted sum of a causal factor over the assignments of `A \ B`. -/
theorem margSum_mul_Q {A B : Finset (Fin n)} (hBA : B ⊆ A) (v : ∀ i, X i)
    (φ : (∀ i, X i) → ℝ) :
    margSum (A \ B) v (fun w => φ w * M.Q A w) =
      M.E (fun u => if ∀ i ∈ B, M.toMech.resp (univ \ A) v u i = v i then
        φ (patch (A \ B) (M.toMech.resp (univ \ A) v u) v) else 0) := by
  refine Eq.trans ?_ (sum_varyOn_mul_P M (A \ B) v φ
    (fun u => ∀ i ∈ B, M.toMech.resp (univ \ A) v u i = v i)
    (fun u => M.toMech.resp (univ \ A) v u))
  unfold margSum
  refine Finset.sum_congr rfl (fun w hw => ?_)
  beta_reduce
  congr 1
  unfold SCM.Q SCM.Pdo
  apply M.P_congr
  intro u
  have hw' := mem_varyOn.mp hw
  have hresp : M.toMech.resp (univ \ A) w u = M.toMech.resp (univ \ A) v u := by
    apply Mech.resp_congr
    intro i hi
    apply hw'
    intro hi'
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hi').1
  rw [hresp]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => h i (Finset.mem_sdiff.mp hi).1⟩
    rw [h i (hBA hi)]
    exact hw' i (fun h' => (Finset.mem_sdiff.mp h').2 hi)
  · rintro ⟨h1, h2⟩ i hi
    by_cases hiB : i ∈ B
    · rw [h1 i hiB]
      exact (hw' i (fun h' => (Finset.mem_sdiff.mp h').2 hiB)).symm
    · exact h2 i (Finset.mem_sdiff.mpr ⟨hi, hiB⟩)

/-- Summing `Q[A]` over the assignments of `A \ B` leaves the probability that, with every
vertex outside `A` fixed, `B` takes its values in `v`. -/
theorem margSum_Q_eq {A B : Finset (Fin n)} (hBA : B ⊆ A) (v : ∀ i, X i) :
    margSum (A \ B) v (M.Q A) =
      M.P (fun u => ∀ i ∈ B, M.toMech.resp (univ \ A) v u i = v i) := by
  have h := margSum_mul_Q M hBA v (fun _ => 1)
  simp only [one_mul] at h
  rw [P_eq_E M]
  exact h

omit [∀ i, Fintype (X i)] in
/-- `Q[C](v)` is the probability that every equation of `C` holds at `v`. -/
theorem Q_eq_P_fix (C : Finset (Fin n)) (v : ∀ i, X i) :
    M.Q C v = M.P (fun u => ∀ i ∈ C, M.toMech.f i v u = v i) := by
  unfold SCM.Q SCM.Pdo
  apply M.P_congr
  intro u
  constructor
  · intro h
    have hz : M.toMech.resp (univ \ C) v u = v := by
      funext i
      by_cases hi : i ∈ C
      · exact h i hi
      · exact Mech.resp_of_mem (by simp [hi])
    intro i hi
    have hi' : i ∉ univ \ C := by simp [hi]
    have key := Mech.resp_of_not_mem (M := M.toMech) (x := v) (u := u) hi'
    rw [hz] at key
    exact key.symm
  · intro h
    have hz : v = M.toMech.resp (univ \ C) v u := by
      apply M.toMech.eq_resp
      intro i
      by_cases hi : i ∈ univ \ C
      · rw [ite_eq_left hi]
      · rw [ite_eq_right hi]
        exact (h i (by simpa using hi)).symm
    intro i _
    rw [← hz]

omit [∀ i, Fintype (X i)] in
/-- An observational cell remains positive after fixing the vertices outside `H`. -/
theorem Q_pos_of_observational_pos (H : Finset (Fin n)) (v : ∀ i, X i)
    (hpos : 0 < M.Q univ v) : 0 < M.Q H v := by
  apply lt_of_lt_of_le hpos
  rw [Q_eq_P_fix M univ v, Q_eq_P_fix M H v]
  exact M.P_mono (fun _ h i _ => h i (Finset.mem_univ i))

omit [DecidableEq L] [∀ i, Fintype (X i)] [∀ i, Inhabited (X i)] [∀ i, DecidableEq (X i)] in
theorem fix_roots (v : ∀ i, X i) (i : Fin n) {u u' : ∀ l, U l}
    (h : ∀ l ∈ M.ex i, u l = u' l) :
    (M.toMech.f i v u = v i ↔ M.toMech.f i v u' = v i) := by
  rw [M.toMech.f_ex i v u u' h]

omit [∀ i, Fintype (X i)] in
theorem Q_empty (v : ∀ i, X i) : M.Q ∅ v = 1 := by
  rw [Q_eq_P_fix, ← P_true M]
  exact M.P_congr (fun u => by simp)

section IndependentEvents

omit [∀ i, Fintype (X i)] [∀ i, Inhabited (X i)] [∀ i, DecidableEq (X i)]

/-- Independence of events that read disjoint blocks of roots. -/
theorem P_and_indep (D : Finset L) {E F : (∀ l, U l) → Prop} [DecidablePred E]
    [DecidablePred F] (hE : ∀ u u', (∀ l ∈ D, u l = u' l) → (E u ↔ E u'))
    (hF : ∀ u u', (∀ l, l ∉ D → u l = u' l) → (F u ↔ F u')) :
    M.P (fun u => E u ∧ F u) = M.P E * M.P F := by
  rw [P_eq_E M (fun u => E u ∧ F u), P_eq_E M E, P_eq_E M F]
  rw [M.E_split D (fun u => if E u ∧ F u then (1 : ℝ) else 0)
    (fun a b => (if E a then (1 : ℝ) else 0) * (if F b then 1 else 0))]
  · have hlin : ∀ a, M.E (fun b => (if E a then (1 : ℝ) else 0) * (if F b then 1 else 0)) =
        (if E a then 1 else 0) * M.E (fun b => if F b then (1 : ℝ) else 0) := by
      intro a
      unfold SCM.E
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    simp_rw [hlin]
    unfold SCM.E
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  · intro a b
    have h1 : E (SCM.merge D a b) ↔ E a := hE _ _ (fun l hl => SCM.merge_of_mem hl)
    have h2 : F (SCM.merge D a b) ↔ F b := hF _ _ (fun l hl => SCM.merge_of_not_mem hl)
    by_cases ha : E a <;> by_cases hb : F b <;> simp [h1, h2, ha, hb]

/-- Independence of finitely many events that read pairwise disjoint blocks of roots. -/
theorem P_forall_indep {ι : Type*} [DecidableEq ι] (s : Finset ι) (E : ι → (∀ l, U l) → Prop)
    [∀ i, DecidablePred (E i)] (D : ι → Finset L)
    (hD : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (D i) (D j))
    (hE : ∀ i ∈ s, ∀ u u', (∀ l ∈ D i, u l = u' l) → (E i u ↔ E i u')) :
    M.P (fun u => ∀ i ∈ s, E i u) = ∏ i ∈ s, M.P (E i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, ← P_true M]
    exact M.P_congr (fun u => by simp)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 : M.P (fun u => ∀ i ∈ insert a s, E i u) =
        M.P (fun u => E a u ∧ ∀ i ∈ s, E i u) :=
      M.P_congr (fun u => Finset.forall_mem_insert a s (fun i => E i u))
    rw [h1, P_and_indep M (D a) (hE a (Finset.mem_insert_self a s))]
    · rw [ih (fun i hi j hj hij => hD i (Finset.mem_insert_of_mem hi) j
        (Finset.mem_insert_of_mem hj) hij) (fun i hi => hE i (Finset.mem_insert_of_mem hi))]
    · intro u u' huu'
      apply forall₂_congr
      intro i hi
      apply hE i (Finset.mem_insert_of_mem hi)
      intro l hl
      apply huu'
      intro hlD
      have hne : a ≠ i := fun h => ha (h ▸ hi)
      exact Finset.disjoint_left.mp (hD a (Finset.mem_insert_self a s) i
        (Finset.mem_insert_of_mem hi) hne) hlD hl

end IndependentEvents

omit [∀ i, Fintype (X i)] in
/-- Lemma 4(i) for two blocks: a set inside `H` splits along a c-component `C` of `G[H]`. -/
theorem Q_split {G : ADMG n} (hG : M.toMech.diag = G) {H C S : Finset (Fin n)}
    (hC : C ∈ G.ccomps H) (hS : S ⊆ H) (v : ∀ i, X i) :
    M.Q S v = M.Q (S ∩ C) v * M.Q (S \ C) v := by
  subst hG
  rw [Q_eq_P_fix M S, Q_eq_P_fix M (S ∩ C), Q_eq_P_fix M (S \ C)]
  have h1 : M.P (fun u => ∀ i ∈ S, M.toMech.f i v u = v i) =
      M.P (fun u => (∀ i ∈ S ∩ C, M.toMech.f i v u = v i) ∧
        ∀ i ∈ S \ C, M.toMech.f i v u = v i) := by
    apply M.P_congr
    intro u
    constructor
    · intro h
      exact ⟨fun i hi => h i (Finset.mem_inter.mp hi).1,
        fun i hi => h i (Finset.mem_sdiff.mp hi).1⟩
    · rintro ⟨h1, h2⟩ i hi
      by_cases hiC : i ∈ C
      · exact h1 i (Finset.mem_inter.mpr ⟨hi, hiC⟩)
      · exact h2 i (Finset.mem_sdiff.mpr ⟨hi, hiC⟩)
  rw [h1]
  apply P_and_indep M (C.biUnion M.ex)
  · intro u u' huu'
    apply forall₂_congr
    intro i hi
    exact fix_roots M v i (fun l hl => huu' l (Finset.mem_biUnion.mpr
      ⟨i, (Finset.mem_inter.mp hi).2, hl⟩))
  · intro u u' huu'
    apply forall₂_congr
    intro i hi
    obtain ⟨hiS, hiC⟩ := Finset.mem_sdiff.mp hi
    apply fix_roots M v i
    intro l hl
    apply huu'
    intro hlD
    obtain ⟨j, hjC, hlj⟩ := Finset.mem_biUnion.mp hlD
    have hij : j ≠ i := fun h => hiC (h ▸ hjC)
    have hbi : M.toMech.diag.bi j i = true := by
      apply decide_eq_true
      exact ⟨hij, ⟨l, Finset.mem_inter.mpr ⟨hlj, hl⟩⟩⟩
    exact hiC (mem_ccomp_of_bi hC hjC (hS hiS) hbi)

/-! ## Tian and Pearl's Lemmas 3 and 4 -/

/-- **R-290-L Lemma 3** (ancestral marginalization): if `C ⊆ C'` and `C` is
an ancestral set in `G[C']`, then `∑_{c' \ C} Q[C'] = Q[C]`. -/
theorem Q_marg_ancestral {G : ADMG n} (hG : M.toMech.diag = G) {C C' : Finset (Fin n)}
    (hCC' : C ⊆ C') (hanc : G.AncestralIn C' C) (v : ∀ i, X i) :
    margSum (C' \ C) v (M.Q C') = M.Q C v := by
  subst hG
  rw [margSum_Q_eq M hCC' v]
  unfold SCM.Q SCM.Pdo
  apply M.P_congr
  intro u
  apply forall₂_congr
  intro i hi
  have hTS : univ \ C' ⊆ univ \ C := Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hCC'
  rw [Mech.resp_restrict hTS v u (fun d hd hdT hpath => (Finset.mem_sdiff.mp hd).2
    (hanc d (by simpa using hdT) i hi hpath))]

omit [∀ i, Fintype (X i)] in
/-- **R-290-L Lemma 4(i)**: `Q[H]` is the product of the causal factors of the
c-components of `G[H]`. -/
theorem Q_prod_ccomps {G : ADMG n} (hG : M.toMech.diag = G) (H : Finset (Fin n))
    (v : ∀ i, X i) : M.Q H v = ∏ C ∈ G.ccomps H, M.Q C v := by
  subst hG
  have hsym : ∀ i j, M.toMech.diag.bi i j = M.toMech.diag.bi j i := M.toMech.diag_wf.2.2.1
  simp only [Q_eq_P_fix M]
  have h1 : M.P (fun u => ∀ i ∈ H, M.toMech.f i v u = v i) =
      M.P (fun u => ∀ C ∈ M.toMech.diag.ccomps H, ∀ i ∈ C, M.toMech.f i v u = v i) := by
    apply M.P_congr
    intro u
    constructor
    · intro h C hC i hi
      exact h i (ccomps_subset hC hi)
    · intro h i hi
      exact h _ (ccOf_mem_ccomps hi) i (mem_ccOf_self H i)
  rw [h1]
  refine (P_congr_inst M _ _ (fun u => Iff.rfl)).trans ((P_forall_indep M
    (M.toMech.diag.ccomps H) (fun C u => ∀ i ∈ C, M.toMech.f i v u = v i)
    (fun C => C.biUnion M.ex) ?_ ?_).trans
    (Finset.prod_congr rfl (fun C _ => P_congr_inst M _ _ (fun u => Iff.rfl))))
  · intro C hC C' hC' hne
    rw [Finset.disjoint_left]
    intro l hl hl'
    obtain ⟨i, hi, hli⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨j, hj, hlj⟩ := Finset.mem_biUnion.mp hl'
    by_cases hij : i = j
    · subst hij
      exact hne (ccomps_eq_of_mem hsym hC hC' hi hj)
    · have hbi : M.toMech.diag.bi i j = true := by
        apply decide_eq_true
        exact ⟨hij, ⟨l, Finset.mem_inter.mpr ⟨hli, hlj⟩⟩⟩
      have hjC : j ∈ C := mem_ccomp_of_bi hC hi (ccomps_subset hC' hj) hbi
      exact hne (ccomps_eq_of_mem hsym hC hC' hjC hj)
  · intro C _ u u' huu'
    apply forall₂_congr
    intro i hi
    exact fix_roots M v i (fun l hl => huu' l (Finset.mem_biUnion.mpr ⟨i, hi, hl⟩))

/-- **R-290-L Lemma 4(ii).** For a topological order of `H`, the prefix ratio product for
a district `C` equals `Q[C]` at every assignment where the selected denominators are
positive. -/
theorem cfac_eq_Q {G : ADMG n} (hG : M.toMech.diag = G) {H C : Finset (Fin n)}
    (hC : C ∈ G.ccomps H) {ord : List (Fin n)} (hord : G.IsTopoOrder H ord) (v : ∀ i, X i)
    (positive : ∀ c ∈ C, 0 < prefixMarg ord H (M.Q H) (ord.idxOf c) v) :
    cfac ord H C (M.Q H) v = M.Q C v := by
  have hCH : C ⊆ H := ccomps_subset hC
  have hmem : ∀ c ∈ C, c ∈ ord := fun c hc => (hord.2.1 c).mpr (hCH hc)
  obtain ⟨gC, hgC⟩ : ∃ g : ℕ → ℝ, ∀ k, g k = M.Q ((ord.take k).toFinset ∩ C) v :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨gN, hgN⟩ : ∃ g : ℕ → ℝ, ∀ k, g k = M.Q ((ord.take k).toFinset \ C) v :=
    ⟨_, fun _ => rfl⟩
  have hsplit : ∀ k, M.Q (ord.take k).toFinset v = gC k * gN k := by
    intro k
    rw [hgC, hgN]
    exact Q_split M hG hC (take_subset_of_topo hord k) v
  have hprefix : ∀ j, prefixMarg ord H (M.Q H) j v = gC j * gN j := by
    intro j
    rw [prefixMarg,
      Q_marg_ancestral M hG (take_subset_of_topo hord j) (take_ancestralIn hord j) v,
      hsplit]
  have hstep : ∀ c ∈ C, gN (ord.idxOf c + 1) = gN (ord.idxOf c) := by
    intro c hc
    have hlt : ord.idxOf c < ord.length := List.idxOf_lt_length_of_mem (hmem c hc)
    rw [hgN, hgN, take_succ_toFinset hlt, List.getElem_idxOf hlt, Finset.insert_sdiff_of_mem _ hc]
  have hgC0 : ∀ k, 0 ≤ gC k := fun k => by
    rw [hgC]
    exact Q_nonneg M _ v
  have hgN0 : ∀ k, 0 ≤ gN k := fun k => by
    rw [hgN]
    exact Q_nonneg M _ v
  have hpos_split : ∀ k, 0 < gC k * gN k → 0 < gC k ∧ 0 < gN k := by
    intro k hk
    constructor
    · rcases (hgC0 k).lt_or_eq with h0 | h0
      · exact h0
      · rw [← h0, zero_mul] at hk
        exact absurd hk (lt_irrefl 0)
    · rcases (hgN0 k).lt_or_eq with h0 | h0
      · exact h0
      · rw [← h0, mul_zero] at hk
        exact absurd hk (lt_irrefl 0)
  have hCfin : (ord.take ord.length).toFinset ∩ C = C := by
    rw [List.take_length]
    exact Finset.inter_eq_right.mpr (fun c hc => List.mem_toFinset.mpr (hmem c hc))
  have hfac : ∀ c ∈ C, 0 < gC (ord.idxOf c) ∧
      prefixMarg ord H (M.Q H) (ord.idxOf c + 1) v /
        prefixMarg ord H (M.Q H) (ord.idxOf c) v =
        gC (ord.idxOf c + 1) / gC (ord.idxOf c) := by
    intro c hc
    have hpos := positive c hc
    rw [hprefix] at hpos
    obtain ⟨hCpos, hNpos⟩ := hpos_split _ hpos
    rw [hprefix, hprefix, hstep c hc]
    exact ⟨hCpos, mul_div_mul_right _ _ (ne_of_gt hNpos)⟩
  have hT : ∀ k, k ≤ ord.length →
      ∏ c ∈ (ord.take k).toFinset ∩ C, (gC (ord.idxOf c + 1) / gC (ord.idxOf c)) = gC k := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [hgC 0, List.take_zero, List.toFinset_nil, Finset.empty_inter, Finset.prod_empty,
        Q_empty M v]
    | succ k ih =>
      intro hk
      have hk' : k < ord.length := hk
      have hidx : ord.idxOf ord[k] = k := List.Nodup.idxOf_getElem hord.1 k hk'
      have hxnot : ord[k] ∉ (ord.take k).toFinset := by
        rw [List.mem_toFinset, List.mem_take_iff_idxOf_lt (List.getElem_mem hk'), hidx]
        exact lt_irrefl k
      rw [take_succ_toFinset hk']
      by_cases hxC : ord[k] ∈ C
      · rw [Finset.insert_inter_of_mem hxC,
          Finset.prod_insert (fun hx => hxnot (Finset.mem_inter.mp hx).1),
          ih (le_of_lt hk'), hidx]
        have hgk : 0 < gC k := by
          have h' := (hfac ord[k] hxC).1
          rwa [hidx] at h'
        rw [div_mul_cancel₀ _ (ne_of_gt hgk)]
      · rw [Finset.insert_inter_of_notMem hxC, ih (le_of_lt hk'), hgC, hgC,
          take_succ_toFinset hk', Finset.insert_inter_of_notMem hxC]
  calc cfac ord H C (M.Q H) v
      = ∏ c ∈ C, (gC (ord.idxOf c + 1) / gC (ord.idxOf c)) :=
        Finset.prod_congr rfl (fun c hc => (hfac c hc).2)
    _ = ∏ c ∈ (ord.take ord.length).toFinset ∩ C,
          (gC (ord.idxOf c + 1) / gC (ord.idxOf c)) := by rw [hCfin]
    _ = gC ord.length := hT ord.length le_rfl
    _ = M.Q C v := by rw [hgC, hCfin]

/-- A positive current cell implies positivity of every prefix marginal of that cell. -/
theorem cfac_eq_Q_of_pos {G : ADMG n} (hG : M.toMech.diag = G) {H C : Finset (Fin n)}
    (hC : C ∈ G.ccomps H) {ord : List (Fin n)} (hord : G.IsTopoOrder H ord) (v : ∀ i, X i)
    (hpos : 0 < M.Q H v) : cfac ord H C (M.Q H) v = M.Q C v := by
  apply cfac_eq_Q M hG hC hord v
  intro c _
  unfold prefixMarg margSum
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := M.Q H)
    (fun w _ => M.Q_nonneg H w) (mem_varyOn.mpr (fun _ _ => rfl)))

end SCM

end Mec

import MecLean.Common.Indep

set_option linter.unusedSectionVars false

/-!
# Edge interventions

A selected directed edge supplies a constant to its receiving mechanism at one parent
argument. Each other argument receives its parent's response on the same unit. Cutting the
selected edges leaves all bidirected edges in place. An ordinary intervention supplies the
same value to every outgoing argument of each intervened vertex.
-/

open Finset

namespace Mec

variable {n : ℕ}

/-- Selected inputs: `(p, v) ∈ F` means that `f_v` receives a constant at its argument `p`. -/
abbrev EdgeSet (n : ℕ) := Finset (Fin n × Fin n)

namespace ADMG

/-- `𝒢_{𝐗_{∗∗}}`: delete the directed edges of `F`; keep every other directed
edge and every bidirected edge. -/
def cutE (G : ADMG n) (F : EdgeSet n) : ADMG n where
  dir p v := G.dir p v && decide ((p, v) ∉ F)
  bi := G.bi

/-- The directed edges of `G` out of `S`: the inputs fixed by the ordinary intervention on `S`. -/
def outE (G : ADMG n) (S : Finset (Fin n)) : EdgeSet n :=
  Finset.univ.filter (fun e : Fin n × Fin n => e.1 ∈ S ∧ G.dir e.1 e.2 = true)

variable {G : ADMG n}

theorem cutE_dir {F : EdgeSet n} {p v : Fin n} :
    (G.cutE F).dir p v = true ↔ G.dir p v = true ∧ (p, v) ∉ F := by
  simp [cutE]

theorem cutE_bi (F : EdgeSet n) : (G.cutE F).bi = G.bi := rfl

theorem mem_outE {S : Finset (Fin n)} {e : Fin n × Fin n} :
    e ∈ G.outE S ↔ e.1 ∈ S ∧ G.dir e.1 e.2 = true := by
  simp [outE]

end ADMG

namespace Mech

variable {X : Fin n → Type} {L : Type} {U : L → Type} (M : Mech n X L U)
  [∀ i, Inhabited (X i)]

/-- The system of `𝓜_{𝐗_{∗∗}}` at `u` (`alg: ctf-realizable-scm`): `f_i` receives `c i j` at
each argument `j` with `(j, i) ∈ F`, and the value of `j` otherwise. -/
def sysE (F : EdgeSet n) (c : Fin n → ∀ p, X p) (u : ∀ l, U l) : ∀ i, (∀ j, X j) → X i :=
  fun i z => M.f i (fun j => if (j, i) ∈ F then c i j else z j) u

theorem sysE_dep (F : EdgeSet n) (c : Fin n → ∀ p, X p) (u : ∀ l, U l) (i : Fin n) :
    DepOn (fun j => M.rank j < M.rank i) (M.sysE F c u i) := by
  intro z z' h
  unfold sysE
  apply M.f_pa
  intro j hj
  show (if (j, i) ∈ F then c i j else z j) = (if (j, i) ∈ F then c i j else z' j)
  split_ifs
  · rfl
  · exact h j (M.pa_rank hj)

/-- The response of the parent-input specification `F` with values `c` at `u`: the solution of
`𝓜_{𝐗_{∗∗}}`. -/
def respE (F : EdgeSet n) (c : Fin n → ∀ p, X p) (u : ∀ l, U l) : ∀ i, X i :=
  sol (M.sysE F c u)

theorem respE_spec (F : EdgeSet n) (c : Fin n → ∀ p, X p) (u : ∀ l, U l) (i : Fin n) :
    M.respE F c u i = M.f i (fun j => if (j, i) ∈ F then c i j else M.respE F c u j) u :=
  sol_spec M.rank (M.sysE_dep F c u) i

/-- Uniqueness: any solution of the system of `𝓜_{𝐗_{∗∗}}` is `respE`. -/
theorem eq_respE (F : EdgeSet n) (c : Fin n → ∀ p, X p) (u : ∀ l, U l) {z : ∀ i, X i}
    (hz : ∀ i, z i = M.f i (fun j => if (j, i) ∈ F then c i j else z j) u) :
    z = M.respE F c u :=
  eq_sol M.rank (M.sysE_dep F c u) hz

variable {M}

/-- Values at pairs outside `F` are irrelevant (edge form of `resp_congr`). -/
theorem respE_congr {F : EdgeSet n} {c c' : Fin n → ∀ p, X p} (u : ∀ l, U l)
    (h : ∀ p v, (p, v) ∈ F → c v p = c' v p) : M.respE F c u = M.respE F c' u := by
  apply M.eq_respE F c' u
  intro i
  rw [M.respE_spec F c u i]
  apply M.f_pa
  intro j _
  show (if (j, i) ∈ F then c i j else M.respE F c u j) =
    (if (j, i) ∈ F then c' i j else M.respE F c u j)
  by_cases hj : (j, i) ∈ F
  · rw [if_pos hj, if_pos hj]
    exact h j i hj
  · rw [if_neg hj, if_neg hj]

/-- A pair `(p, v)` with `p` not a listed argument of `f_v` fixes nothing.  Hence statements may
quantify over all edge sets: for a model conforming to `𝒢`, only the edges of `𝒢` matter. -/
theorem respE_filter_pa (F : EdgeSet n) (c : Fin n → ∀ p, X p) (u : ∀ l, U l) :
    M.respE (F.filter (fun e => e.1 ∈ M.pa e.2)) c u = M.respE F c u := by
  apply M.eq_respE F c u
  intro i
  rw [M.respE_spec (F.filter (fun e => e.1 ∈ M.pa e.2)) c u i]
  apply M.f_pa
  intro j hj
  have hmem : (j, i) ∈ F.filter (fun e => e.1 ∈ M.pa e.2) ↔ (j, i) ∈ F := by
    rw [Finset.mem_filter]
    exact ⟨fun h => h.1, fun h => ⟨h, hj⟩⟩
  show (if (j, i) ∈ F.filter (fun e => e.1 ∈ M.pa e.2) then c i j
      else M.respE (F.filter (fun e => e.1 ∈ M.pa e.2)) c u j) =
    (if (j, i) ∈ F then c i j else M.respE (F.filter (fun e => e.1 ∈ M.pa e.2)) c u j)
  by_cases hF : (j, i) ∈ F
  · rw [if_pos (hmem.mpr hF), if_pos hF]
  · rw [if_neg (fun h => hF (hmem.mp h)), if_neg hF]

/-- Composition (edge form of `resp_extend`, the unit-level form of ctf-Rule 1):
fixing further inputs at the current values of their sources changes nothing. -/
theorem respE_extend {F F' : EdgeSet n} (hF : F ⊆ F') (c c' : Fin n → ∀ p, X p)
    (u : ∀ l, U l) (hc : ∀ p v, (p, v) ∈ F → c' v p = c v p)
    (hc' : ∀ p v, (p, v) ∈ F' → (p, v) ∉ F → c' v p = M.respE F c u p) :
    M.respE F' c' u = M.respE F c u := by
  symm
  apply M.eq_respE F' c' u
  intro i
  rw [M.respE_spec F c u i]
  apply M.f_pa
  intro j _
  show (if (j, i) ∈ F then c i j else M.respE F c u j) =
    (if (j, i) ∈ F' then c' i j else M.respE F c u j)
  by_cases h1 : (j, i) ∈ F
  · rw [if_pos h1, if_pos (hF h1), hc j i h1]
  · rw [if_neg h1]
    by_cases h2 : (j, i) ∈ F'
    · rw [if_pos h2, hc' j i h2 h1]
    · rw [if_neg h2]

variable [DecidableEq L]

/-- With no selected input, the response is the natural one. -/
theorem respE_empty (c : Fin n → ∀ p, X p) (x : ∀ i, X i) (u : ∀ l, U l) :
    M.respE ∅ c u = M.resp ∅ x u := by
  symm
  apply M.eq_respE ∅ c u
  intro i
  rw [Mech.resp_of_not_mem (Finset.notMem_empty i)]
  apply M.f_pa
  intro j _
  show M.resp ∅ x u j = (if (j, i) ∈ (∅ : EdgeSet n) then c i j else M.resp ∅ x u j)
  rw [if_neg (Finset.notMem_empty (j, i))]

/-- **Agreement lemma for specifications** (edge form of `resp_agree`).  Let `Δ` contain every
vertex whose fixed inputs differ between `(F₁, c₁)` and `(F₂, c₂)`.  The two responses agree at
every vertex not reached from `Δ` by a directed path of the diagram with the inputs fixed in both
specifications deleted. -/
theorem respE_agree {F₁ F₂ : EdgeSet n} {c₁ c₂ : Fin n → ∀ p, X p} (u : ∀ l, U l)
    (Δ : Fin n → Prop)
    (hΔ : ∀ i, ¬ Δ i → ∀ p ∈ M.pa i,
      ((p, i) ∈ F₁ ↔ (p, i) ∈ F₂) ∧ ((p, i) ∈ F₁ → c₁ i p = c₂ i p))
    {v : Fin n} (hv : ∀ d, Δ d → ¬ (M.diag.cutE (F₁ ∩ F₂)).Anc d v) :
    M.respE F₁ c₁ u v = M.respE F₂ c₂ u v := by
  revert hv
  refine rank_induction M.rank (P := fun v => (∀ d, Δ d → ¬ (M.diag.cutE (F₁ ∩ F₂)).Anc d v) →
    M.respE F₁ c₁ u v = M.respE F₂ c₂ u v) (fun w ih hw => ?_) v
  have hnw : ¬ Δ w := fun h => hw w h (Reach.refl w)
  rw [M.respE_spec F₁ c₁ u w, M.respE_spec F₂ c₂ u w]
  apply M.f_pa
  intro j hj
  obtain ⟨hmem, hval⟩ := hΔ w hnw j hj
  show (if (j, w) ∈ F₁ then c₁ w j else M.respE F₁ c₁ u j) =
    (if (j, w) ∈ F₂ then c₂ w j else M.respE F₂ c₂ u j)
  by_cases h1 : (j, w) ∈ F₁
  · rw [if_pos h1, if_pos (hmem.mp h1)]
    exact hval h1
  · rw [if_neg h1, if_neg (fun h => h1 (hmem.mpr h))]
    apply ih j (M.pa_rank hj)
    intro d hd hreach
    have hedge : (M.diag.cutE (F₁ ∩ F₂)).dir j w = true :=
      ADMG.cutE_dir.mpr ⟨(M.diag_dir).mpr hj, fun h => h1 (Finset.mem_inter.mp h).1⟩
    exact hw d hd (Reach.tail hreach hedge (Finset.notMem_empty w))

/-- Restriction (edge form of `resp_restrict`, the unit-level form of ctf-Rule 3):
selected inputs whose receivers have no directed path to `y` in the diagram with the inputs of
`F'` deleted can be dropped. -/
theorem respE_restrict {F F' : EdgeSet n} (hF : F' ⊆ F) (c : Fin n → ∀ p, X p)
    (u : ∀ l, U l) {y : Fin n}
    (h : ∀ p v, (p, v) ∈ F → (p, v) ∉ F' → p ∈ M.pa v → ¬ (M.diag.cutE F').Anc v y) :
    M.respE F c u y = M.respE F' c u y := by
  refine respE_agree u (fun d => ∃ p ∈ M.pa d, (p, d) ∈ F ∧ (p, d) ∉ F') ?_ ?_
  · intro i hi p hp
    refine ⟨⟨fun hpF => ?_, fun hpF' => hF hpF'⟩, fun _ => rfl⟩
    by_contra hpF'
    exact hi ⟨p, hp, hpF, hpF'⟩
  · rintro d ⟨p, hp, hpF, hpF'⟩
    rw [Finset.inter_eq_right.mpr hF]
    exact h p d hpF hpF' hp

/-- The response of `v` reads only the roots of the vertices with a directed path to `v` in the
diagram with the fixed inputs deleted (edge form of `resp_roots`). -/
theorem respE_roots {F : EdgeSet n} (c : Fin n → ∀ p, X p) {u u' : ∀ l, U l} {v : Fin n}
    (h : ∀ w, (M.diag.cutE F).Anc w v → ∀ l ∈ M.ex w, u l = u' l) :
    M.respE F c u v = M.respE F c u' v := by
  revert h
  refine rank_induction M.rank (P := fun v => (∀ w, (M.diag.cutE F).Anc w v →
    ∀ l ∈ M.ex w, u l = u' l) → M.respE F c u v = M.respE F c u' v) (fun v ih h => ?_) v
  rw [M.respE_spec F c u v, M.respE_spec F c u' v, M.f_ex v _ u u' (h v (Reach.refl v))]
  apply M.f_pa
  intro j hj
  show (if (j, v) ∈ F then c v j else M.respE F c u j) =
    (if (j, v) ∈ F then c v j else M.respE F c u' j)
  by_cases hjv : (j, v) ∈ F
  · rw [if_pos hjv, if_pos hjv]
  · rw [if_neg hjv, if_neg hjv]
    apply ih j (M.pa_rank hj)
    intro w hw
    have hedge : (M.diag.cutE F).dir j v = true :=
      ADMG.cutE_dir.mpr ⟨(M.diag_dir).mpr hj, hjv⟩
    exact h w (Reach.tail hw hedge (Finset.notMem_empty v))

/-- An ordinary intervention `do(S = x)` is the specification that fixes every outgoing input of
`S` to the value of its source (proof of `cor: l2 dominance`). -/
theorem resp_eq_respE (S : Finset (Fin n)) (x : ∀ i, X i) (u : ∀ l, U l) {v : Fin n}
    (hv : v ∉ S) : M.resp S x u v = M.respE (M.diag.outE S) (fun _ j => x j) u v := by
  revert hv
  refine rank_induction M.rank (P := fun v => v ∉ S →
    M.resp S x u v = M.respE (M.diag.outE S) (fun _ k => x k) u v) (fun v ih hv => ?_) v
  rw [M.resp_of_not_mem hv, M.respE_spec (M.diag.outE S) (fun _ k => x k) u v]
  apply M.f_pa
  intro j hj
  show M.resp S x u j =
    (if (j, v) ∈ M.diag.outE S then x j else M.respE (M.diag.outE S) (fun _ k => x k) u j)
  have hdir : M.diag.dir j v = true := (M.diag_dir).mpr hj
  by_cases hjS : j ∈ S
  · have hmem : (j, v) ∈ M.diag.outE S := ADMG.mem_outE.mpr ⟨hjS, hdir⟩
    rw [if_pos hmem, Mech.resp_of_mem hjS]
  · have hmem : (j, v) ∉ M.diag.outE S := fun h => hjS (ADMG.mem_outE.mp h).1
    rw [if_neg hmem]
    exact ih j (M.pa_rank hj) hjS

end Mech

namespace Model

variable (m : Model n)

/-- Mean reward `𝔼[r(Y_{𝐗_{∗∗}})]` of the specification `F` with values `c`. -/
noncomputable def muE (y : Fin n) (r : m.X y → ℝ) (F : EdgeSet n) (c : Fin n → ∀ p, m.X p) : ℝ :=
  m.scm.E (fun u => r (m.scm.toMech.respE F c u y))

/-- Best mean reward over the values of the selected inputs, `μ_{𝐗_{∗∗}^∗}`. -/
noncomputable def bestE (y : Fin n) (r : m.X y → ℝ) (F : EdgeSet n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun c : Fin n → ∀ p, m.X p => m.muE y r F c)

/-- Mean reward of the outer-target action `(S, F)`: every target in `S` receives its value in
the world of `F` with values `c`; the outer system is otherwise natural. -/
noncomputable def muSet (y : Fin n) (r : m.X y → ℝ) (S : Finset (Fin n)) (F : EdgeSet n)
    (c : Fin n → ∀ p, m.X p) : ℝ :=
  m.scm.E (fun u => r (m.scm.toMech.resp S (m.scm.toMech.respE F c u) u y))

theorem muE_le_bestE (y : Fin n) (r : m.X y → ℝ) (F : EdgeSet n) (c : Fin n → ∀ p, m.X p) :
    m.muE y r F c ≤ m.bestE y r F :=
  Finset.le_sup' (fun c : Fin n → ∀ p, m.X p => m.muE y r F c) (Finset.mem_univ c)

theorem exists_bestE (y : Fin n) (r : m.X y → ℝ) (F : EdgeSet n) :
    ∃ c, m.muE y r F c = m.bestE y r F := by
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun c : Fin n → ∀ p, m.X p => m.muE y r F c)
  exact ⟨c, hc.symm⟩

theorem bestE_le {y : Fin n} {r : m.X y → ℝ} {F : EdgeSet n} {b : ℝ}
    (h : ∀ c, m.muE y r F c ≤ b) : m.bestE y r F ≤ b :=
  Finset.sup'_le _ _ (fun c _ => h c)

/-- Pointwise equal rewards give equal means. -/
theorem muE_congr {y : Fin n} {r : m.X y → ℝ} {F F' : EdgeSet n} {c c' : Fin n → ∀ p, m.X p}
    (h : ∀ u, m.scm.toMech.respE F c u y = m.scm.toMech.respE F' c' u y) :
    m.muE y r F c = m.muE y r F' c' := by
  unfold muE
  exact m.scm.E_congr (fun u => by rw [h u])

end Model

end Mec

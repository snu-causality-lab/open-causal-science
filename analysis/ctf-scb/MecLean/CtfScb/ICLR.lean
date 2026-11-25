import MecLean.CtfScb.Unnested
import MecLean.CtfScb.POMIS

set_option linter.unusedSectionVars false

/-!
# Checks of statements in Park and Lee (ICLR 2026)

The source is the [ICLR proceedings PDF](https://proceedings.iclr.cc/paper_files/paper/2026/file/da80970c6ca6967f2a4de6f2e13c4bae-Paper-Conference.pdf).
The symbolic labels below identify four exact examples.

* `C1`: Corollary 3 and Theorem 2, p. 8, with the printed regime graph.
* `N1`: Proposition 1, p. 4, necessity of the ancestry test.
* `N4`: direct inputs of the reward mechanism, Algorithm 1 (p. 8), Algorithm 2 (p. 28)
  and the conversion discussed in Appendix F.6.
* `C5`: literal uniqueness in Proposition 2 and Corollary 2, p. 7.
-/

open Finset

namespace Mec.CtfScb.ICLR

open Mec Mec.ScbMec Mec.Scb2018

variable {n : ℕ}

/-- `𝐕^† = 𝐕(An(Y_𝐱, 𝐗_∗))`: the reward term contributes `An(Y)_{𝒢_{\underline 𝐗}}`,
which is `diagH G y 𝐗`, and each target term its computation. -/
def regimeVertices (G : ADMG n) (y : Fin n) (A : UCtf n) : Finset (Fin n) :=
  diagH G y A.tgt ∪ A.tgt.biUnion (fun i => A.comp G i)

/-- The ICLR's counterfactual regime graph `𝓗_{𝐗_∗} = ⟨𝐕^†, 𝐄(𝒢[𝐕^†])⟩`. -/
def regimeGraph (G : ADMG n) (y : Fin n) (A : UCtf n) : ADMG n :=
  Alg.restrict G (regimeVertices G y A)

/-- `IB(𝓗_{𝐗_∗}, Y)` for the ICLR's regime graph. -/
def regimeIB (G : ADMG n) (y : Fin n) (A : UCtf n) : Finset (Fin n) :=
  Alg.ib (regimeGraph G y A) y ∅

/-! ## C-1: the ICLR's regime graph -/

namespace C1

abbrev A : Fin 3 := 0
abbrev B : Fin 3 := 1
abbrev Y : Fin 3 := 2

/-- `A → B → Y`, `A → Y`, `A ↔ Y`. -/
def G : ADMG 3 where
  dir i j := decide ((i = A ∧ j = B) ∨ (i = B ∧ j = Y) ∨ (i = A ∧ j = Y))
  bi i j := decide ((i = A ∧ j = Y) ∨ (i = Y ∧ j = A))

theorem G_wf : G.WF := by decide +kernel

/-- `{B_a}`. -/
def act : UCtf 3 := ⟨{B}, fun _ => {A}⟩

/-- `𝐕^† = {A, B, Y}`, so the ICLR's regime graph is `𝒢` itself and its border is empty, while the
corrected regime graph deletes `A → B` and has border `{B}`.  `{B_a}` satisfies both conditions of
the ICLR's Thm. 1.  The ICLR graph keeps `A → B`, which the diagram of
`𝓜_{𝐗_∗}` lacks (Cor. 3). -/
theorem graph : regimeVertices G Y act = {A, B, Y} ∧ regimeIB G Y act = ∅ ∧
    act.specOf G = {(A, B)} ∧ ctfIB G Y {(A, B)} = {B} ∧ AncCrit G Y {B} ∧
    Cond2 G {B} {(A, B)} B ∧ (regimeGraph G Y act).dir A B = true ∧
    (G.cutE (act.specOf G)).dir A B = false := by
  decide +kernel

/-- **The ICLR's Thm. 2 is false with its regime graph**:
`{B_a}` is a realizable ctf-MIS whose ICLR regime graph has an empty border, but it is not a
ctf-POMIS: in every model conforming to `𝒢`, the ordinary intervention on `B` is at least as good.
That competitor is itself a ctf-MIS, so the conclusion also holds for the ICLR's Def. 4, which compares only ctf-MISs. -/
theorem iclr_thm2_false : regimeIB G Y act = ∅ ∧
    (∀ {Ω : Fin 3 → Type} (c : Fin 3 → ∀ j, Ω j), act.Realizable G Y c) ∧
    CtfMIS G Y {B} {(A, B)} ∧ ¬ CtfPOMIS G Y {(A, B)} ∧
    ∀ m : Model 3, ConfDiag G m → ∀ r : m.X Y → ℝ, m.bestE Y r {(A, B)} ≤ m.best Y r {B} := by
  obtain ⟨-, hIB, -, hctfIB, -, -, -, -⟩ := graph
  -- A single target: the consistency of subscript values is trivial.
  have hreal : ∀ {Ω : Fin 3 → Type} (c : Fin 3 → ∀ j, Ω j), act.Realizable G Y c := by
    intro Ω c
    refine ⟨⟨by decide +kernel, ?_⟩, by decide +kernel⟩
    intro i hi j hj v _ _ w _
    have hi' : i = B := Finset.mem_singleton.mp hi
    have hj' : j = B := Finset.mem_singleton.mp hj
    rw [hi', hj']
  -- Border mixture (`bestE_le_bestE_border`) with the territory `{A, Y}`, then the specification
  -- fixing `A → B` and `B → Y` is the ordinary intervention on `B` on every unit.
  have hbest : ∀ m : Model 3, ConfDiag G m → ∀ r : m.X Y → ℝ,
      m.bestE Y r {(A, B)} ≤ m.best Y r {B} := by
    intro m hm r
    have hm' : m.scm.toMech.diag = G := hm
    have hT : DiagUCT (G.cutE {(A, B)}) Y ∅ {A, Y} := by decide +kernel
    have hbE : ({(A, B)} ∪ borderEdges G {(A, B)} {A, Y} : EdgeSet 3) = {(A, B), (B, Y)} := by
      decide +kernel
    have hle := bestE_le_bestE_border hT m hm r
    rw [hbE] at hle
    have hdirY : ∀ j : Fin 3, G.dir j Y = true → j = A ∨ j = B := by decide +kernel
    have hdirA : ∀ j : Fin 3, G.dir j A = false := by decide +kernel
    have hAY : ((A, Y) : Fin 3 × Fin 3) ∉ ({(A, B), (B, Y)} : EdgeSet 3) := by decide +kernel
    have hBY : ((B, Y) : Fin 3 × Fin 3) ∈ ({(A, B), (B, Y)} : EdgeSet 3) := by decide +kernel
    have hYB : Y ∉ ({B} : Finset (Fin 3)) := by decide +kernel
    have hAB : A ∉ ({B} : Finset (Fin 3)) := by decide +kernel
    have hBB : B ∈ ({B} : Finset (Fin 3)) := Finset.mem_singleton_self B
    have key : ∀ (c : Fin 3 → ∀ p, m.X p) (u : ∀ l, m.U l),
        m.scm.toMech.respE {(A, B), (B, Y)} c u Y = m.scm.toMech.resp {B} (c Y) u Y := by
      intro c u
      rw [m.scm.toMech.respE_spec, m.scm.toMech.resp_of_not_mem hYB]
      apply m.scm.toMech.f_pa
      intro j hj
      show (if (j, Y) ∈ ({(A, B), (B, Y)} : EdgeSet 3) then c Y j
          else m.scm.toMech.respE {(A, B), (B, Y)} c u j) = m.scm.toMech.resp {B} (c Y) u j
      rcases hdirY j ((mem_pa_iff_of_diag_eq hm').mp hj) with rfl | rfl
      · rw [ite_eq_right hAY, m.scm.toMech.respE_spec, m.scm.toMech.resp_of_not_mem hAB]
        apply m.scm.toMech.f_pa
        intro k hk
        exfalso
        have hk' := (mem_pa_iff_of_diag_eq hm').mp hk
        rw [hdirA k] at hk'
        exact Bool.false_ne_true hk'
      · rw [ite_eq_left hBY, m.scm.toMech.resp_of_mem hBB]
    refine hle.trans (m.bestE_le (fun c => ?_))
    have heq : m.muE Y r {(A, B), (B, Y)} c = m.mu Y r {B} (c Y) := by
      unfold Model.muE Model.mu
      exact m.scm.E_congr (fun u => congrArg r (key c u))
    exact heq.trans_le (m.mu_le_best Y r {B} (c Y))
  exact ⟨hIB, hreal, (ctfMIS_iff G_wf (by decide +kernel)).mpr (by decide +kernel),
    fun h => Finset.singleton_ne_empty B (hctfIB.symm.trans (ctfPomis_onlyif G_wf h)), hbest⟩

end C1

/-! ## N1: the ICLR's Prop. 1, "only if" -/

namespace N1

abbrev W : Fin 5 := 0
abbrev A : Fin 5 := 1
abbrev U : Fin 5 := 2
abbrev B : Fin 5 := 3
abbrev Y : Fin 5 := 4

/-- `W → A → U → Y`, `U → B → Y`. -/
def G : ADMG 5 where
  dir i j := decide ((i = W ∧ j = A) ∨ (i = A ∧ j = U) ∨ (i = U ∧ j = Y) ∨ (i = U ∧ j = B) ∨
    (i = B ∧ j = Y))
  bi _ _ := false

theorem G_wf : G.WF := by decide +kernel

/-- `{A_w, B_w}`. -/
def act : UCtf 5 := ⟨{A, B}, fun _ => {W}⟩

/-- `An(Y_{ab}, A_w, B_w)` contains `U_a` (from the reward term) and `U_w` (from `B_w`): `U` is
needed by the reward with minimized subscript `{A}` and by `B_w` with `{W}`.  The outer-target
action `({A, B}, {W → A})` is nevertheless realizable. -/
theorem graph : act.osub G U = {A} ∧ U ∈ act.comp G B ∧ act.msub G B U = {W} ∧
    act.SameVars G ∧ act.specOf G = {(W, A)} ∧ Realizable G Y {A, B} (act.specOf G) := by
  decide +kernel

/-- **The "only if" part of the ICLR's Prop. 1 is false**:
`{A_w, B_w}` fails the test on `An(Y_𝐱, 𝐗_∗)` for every subscript value, yet it is realizable
whenever the two terms use the same `w`, and its reward is `Y_w` on every unit, so
`P(Y_{𝐗_∗}) = P(Y_w)` is realizable. -/
theorem iclr_prop1_onlyIf_false :
    (∀ {Ω : Fin 5 → Type} (c : Fin 5 → ∀ j, Ω j), ¬ act.NoConflict G Y c) ∧
    (∀ {Ω : Fin 5 → Type} (c : Fin 5 → ∀ j, Ω j), c A W = c B W → act.Realizable G Y c) ∧
    ∀ m : Model 5, ConfDiag G m → ∀ (w : ∀ i, m.X i) (u : ∀ l, m.U l),
      act.reward m.scm.toMech (fun _ => w) u Y = m.scm.toMech.resp {W} w u Y := by
  obtain ⟨hosub, hcomp, -, hsv, -, hreal⟩ := graph
  have hB : B ∈ act.tgt := by decide +kernel
  have hU : U ∉ act.tgt := by decide +kernel
  have hUY : G.AncAvoid act.tgt U Y := by decide +kernel
  have htgt : ∀ k ∈ act.tgt, k = A ∨ k = B := by decide +kernel
  -- `U` is needed by the reward term with the minimized subscript `{A}`.
  have hNC : ∀ {Ω : Fin 5 → Type} (c : Fin 5 → ∀ j, Ω j), ¬ act.NoConflict G Y c := by
    intro Ω c hnc
    have h0 := (hnc.2 B hB U hU hUY hcomp).1
    rw [hosub] at h0
    exact Finset.singleton_ne_empty A h0
  -- Every minimized subscript is `{W}`, so consistency asks only `c A W = c B W`.
  have hR : ∀ {Ω : Fin 5 → Type} (c : Fin 5 → ∀ j, Ω j), c A W = c B W →
      act.Realizable G Y c := by
    intro Ω c hc
    refine ⟨⟨hsv, ?_⟩, hreal⟩
    intro i hi j hj v _ _ x hx
    have hxW : x = W := Finset.mem_singleton.mp (UCtf.msub_subset hx)
    rw [hxW]
    rcases htgt i hi with rfl | rfl <;> rcases htgt j hj with rfl | rfl
    · rfl
    · exact hc
    · exact hc.symm
    · rfl
  -- The nested reward fixes `A` and `B` at their values in `𝓜_w`; `W` reaches `Y` only through
  -- `A`, so this is the outer system of `{W, A, B}` with those values, that is, `𝓜_w` itself.
  have hpt : ∀ m : Model 5, ConfDiag G m → ∀ (w : ∀ i, m.X i) (u : ∀ l, m.U l),
      act.reward m.scm.toMech (fun _ => w) u Y = m.scm.toMech.resp {W} w u Y := by
    intro m hm w u
    have hm' : m.scm.toMech.diag = G := hm
    have hsub1 : ({W} : Finset (Fin 5)) ⊆ {W, A, B} := by decide +kernel
    have hsub2 : ({A, B} : Finset (Fin 5)) ⊆ {W, A, B} := by decide +kernel
    have hW1 : W ∈ ({W} : Finset (Fin 5)) := Finset.mem_singleton_self W
    have hfact : ∀ z ∈ ({W, A, B} : Finset (Fin 5)), G.AncAvoid {W, A, B} z Y →
        z ∈ ({A, B} : Finset (Fin 5)) := by decide +kernel
    have hT : ∀ z ∈ ({W, A, B} : Finset (Fin 5)),
        m.scm.toMech.diag.AncAvoid {W, A, B} z Y → z ∈ ({A, B} : Finset (Fin 5)) := by
      rw [hm']
      exact hfact
    have h1 : m.scm.toMech.resp {W, A, B} (m.scm.toMech.resp {W} w u) u =
        m.scm.toMech.resp {W} w u :=
      Mech.resp_extend hsub1 w (m.scm.toMech.resp {W} w u) u
        (fun i hi => by
          rw [Finset.mem_singleton.mp hi]
          exact m.scm.toMech.resp_of_mem hW1)
        (fun i _ _ => rfl)
    have h2 := Mech.resp_core hsub2 hT (m.scm.toMech.resp {W} w u) u
    show m.scm.toMech.resp {A, B} (m.scm.toMech.resp {W} w u) u Y = m.scm.toMech.resp {W} w u Y
    exact h2.symm.trans (congrFun h1 Y)
  exact ⟨hNC, hR, hpt⟩

end N1

/-! ## N4: selected inputs of `f_Y` in the ICLR's algorithm -/

namespace N4

abbrev W : Fin 3 := 0
abbrev C : Fin 3 := 1
abbrev Y : Fin 3 := 2

/-- `W → Y`, `W → C → Y`, `W ↔ Y`. -/
def G : ADMG 3 where
  dir i j := decide ((i = W ∧ j = Y) ∨ (i = W ∧ j = C) ∨ (i = C ∧ j = Y))
  bi i j := decide ((i = W ∧ j = Y) ∨ (i = Y ∧ j = W))

theorem G_wf : G.WF := by decide +kernel

/-- The choice "fix `W → Y`" passes the border test.  Replacing `Y_{Y_w}` by `W_w` gives `do(W = w)`, whose border is `{C}`; dropping the term gives the
empty action, which the empty choice already returns.  The corrected algorithm returns
`{W → Y}` itself. -/
theorem graph : ctfIB G Y {(W, Y)} = ∅ ∧ ctfIB G Y (G.outE {W}) = {C} ∧ ctfIB G Y ∅ = ∅ ∧
    relevant G Y {(W, Y)} = {(W, Y)} ∧
    ctfPOMISs G Y = {∅, {(C, Y)}, {(W, Y)}, {(C, Y), (W, Y)}} := by
  decide +kernel

/-- `{W → Y}` and the empty action are ctf-POMISs; `do(W = w)` is not. -/
theorem pomis : CtfPOMIS G Y {(W, Y)} ∧ ¬ CtfPOMIS G Y (G.outE {W}) ∧ CtfPOMIS G Y ∅ := by
  obtain ⟨h1, h2, h3, -, -⟩ := graph
  exact ⟨(ctfPomis_iff G_wf).mpr h1,
    fun h => Finset.singleton_ne_empty C (h2.symm.trans ((ctfPomis_iff G_wf).mp h)),
    (ctfPomis_iff G_wf).mpr h3⟩

end N4

/-! ## C-5: "the only ctf-POMIS" -/

namespace C5

abbrev X : Fin 3 := 0
abbrev Z : Fin 3 := 1
abbrev Y : Fin 3 := 2

/-- `X → Y`, `X → Z`. -/
def G : ADMG 3 where
  dir i j := decide ((i = X ∧ j = Y) ∨ (i = X ∧ j = Z))
  bi _ _ := false

theorem G_wf : G.WF := by decide +kernel

/-- **"`Pa(Y)_𝒢` is the only ctf-POMIS" holds only up to equivalence**: in this Markovian diagram the inputs of `f_Y` and the ordinary intervention on `X` are two
distinct ctf-POMISs, and they are equivalent. -/
theorem iclr_prop2_literal_false : CtfPOMIS G Y (inEdges G Y) ∧ CtfPOMIS G Y (G.outE {X}) ∧
    inEdges G Y ≠ G.outE {X} ∧ SpecEquiv G Y (inEdges G Y) (G.outE {X}) := by
  have h1 : ctfIB G Y (inEdges G Y) = ∅ := by decide +kernel
  have h2 : ctfIB G Y (G.outE {X}) = ∅ := by decide +kernel
  have h3 : inEdges G Y ≠ G.outE {X} := by decide +kernel
  have h4 : relevant G Y (inEdges G Y) = relevant G Y (G.outE {X}) := by decide +kernel
  exact ⟨(ctfPomis_iff G_wf).mpr h1, (ctfPomis_iff G_wf).mpr h2, h3,
    specEquiv_of_relevant_eq h4⟩

end C5

end Mec.CtfScb.ICLR

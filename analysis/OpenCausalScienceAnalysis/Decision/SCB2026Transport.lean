import OpenCausalScienceAnalysis.Decision.SCB2019Theorem4
import OpenCausalScienceAnalysis.Identification.QFactor

/-!
# On Transportability for Structural Causal Bandits

Park and Lee (2026), Proposition 1 and Appendix C.1. For `C ⊆ D`, the event
that the response on `D` equals `v` under `do(v \ D)` is the intersection of
two events. The first is the response on `C` under `do(v \ C)` matching `v`.
The second is the response on `D \ C` under `do(v \ D)` matching `v`.
Composition of interventions identifies the outcomes in the intersection.
The lower and upper bounds follow by monotonicity and the mass of the second
event's complement. Ancestral marginalization then transports the bounds on
an intermediate factor using the invariant target cell in Eq. (27).

Source: https://proceedings.mlr.press/v337/park26a.html
-/

namespace OpenCausalScienceAnalysis.Scb2026Transport

open Finset Mec Mec.ScbMec

variable {n : ℕ}

private theorem intersection_bounds (m : Model n) (E F : (∀ l, m.U l) → Prop)
    [DecidablePred E] [DecidablePred F] :
    m.scm.P (fun u => E u ∧ F u) ≤ m.scm.P E ∧
      m.scm.P E ≤ m.scm.P (fun u => E u ∧ F u) + 1 - m.scm.P F := by
  refine ⟨m.scm.P_mono (fun _ h => h.1), ?_⟩
  have h := calc
    m.scm.P E + m.scm.P F =
        ∑ u, ((if E u then m.scm.prob u else 0) + (if F u then m.scm.prob u else 0)) := by
      simp only [SCM.P, Finset.sum_add_distrib]
    _ ≤ ∑ u, ((if E u ∧ F u then m.scm.prob u else 0) + m.scm.prob u) := by
      exact Finset.sum_le_sum (fun u _ => by
        by_cases eh : E u <;> by_cases fh : F u <;> simp [eh, fh, m.scm.prob_nonneg u])
    _ = m.scm.P (fun u => E u ∧ F u) + 1 := by
      simp only [SCM.P, Finset.sum_add_distrib, m.scm.sum_prob]
  linarith

/-- Appendix C.1, Eq. (47) with its lower bound. The intervened assignment and
the joint response under the less extensive intervention share the same exogenous world. -/
theorem nested_factor_bounds (m : Model n) {A D : Finset (Fin n)} (hAD : A ⊆ D)
    (v : ∀ i, m.X i) :
    m.scm.Q D v ≤ m.scm.Q A v ∧
      m.scm.Q A v ≤ m.scm.Q D v + 1 - margSum A v (m.scm.Q D) := by
  classical
  let E : (∀ l, m.U l) → Prop :=
    fun u => ∀ i ∈ A, m.scm.toMech.resp (univ \ A) v u i = v i
  let F : (∀ l, m.U l) → Prop :=
    fun u => ∀ i ∈ D \ A, m.scm.toMech.resp (univ \ D) v u i = v i
  have extension : univ \ D ⊆ univ \ A := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, fun h => (Finset.mem_sdiff.mp hi).2 (hAD h)⟩
  have compose (u : ∀ l, m.U l) (h : F u) :
      m.scm.toMech.resp (univ \ A) v u = m.scm.toMech.resp (univ \ D) v u := by
    refine m.scm.toMech.resp_extend extension v v u (fun _ _ => rfl) ?_
    intro i hi hn
    have hiD : i ∈ D := by simpa using hn
    exact (h i (Finset.mem_sdiff.mpr ⟨hiD, (Finset.mem_sdiff.mp hi).2⟩)).symm
  have joint : m.scm.Q D v = m.scm.P (fun u => E u ∧ F u) := by
    unfold SCM.Q SCM.Pdo
    apply m.scm.P_congr
    intro u
    constructor
    · intro whole
      have hF : F u := fun i hi => whole i (Finset.mem_sdiff.mp hi).1
      refine ⟨fun i hi => ?_, hF⟩
      rw [compose u hF]
      exact whole i (hAD hi)
    · rintro ⟨hE, hF⟩ i hi
      by_cases hiA : i ∈ A
      · rw [← compose u hF]
        exact hE i hiA
      · exact hF i (Finset.mem_sdiff.mpr ⟨hi, hiA⟩)
  have single : m.scm.Q A v = m.scm.P E := by
    unfold SCM.Q SCM.Pdo
    exact m.scm.P_congr (fun _ => Iff.rfl)
  have split : D \ (D \ A) = A := by
    ext i
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hi, hnot⟩
      by_contra h
      exact hnot ⟨hi, h⟩
    · intro hi
      exact ⟨hAD hi, fun h => h.2 hi⟩
  have marginal : margSum A v (m.scm.Q D) = m.scm.P F := by
    calc
      _ = margSum (D \ (D \ A)) v (m.scm.Q D) := by rw [split]
      _ = m.scm.P (fun u => ∀ i ∈ D \ A, m.scm.toMech.resp (univ \ D) v u i = v i) :=
        m.scm.margSum_Q_eq Finset.sdiff_subset v
      _ = _ := m.scm.P_congr (fun _ => Iff.rfl)
  rw [joint, single, marginal]
  exact intersection_bounds m E F

/-- Proposition 1, Eqs. (10)–(11). `targetFactor` is the target `Q[C](v)`
and `invariant` supplies its equality to the source `Q[C](v)` from Eq. (27).
The finite model proves both bounds for any source model obeying the diagram
and ancestral premise. Identifiability of the supplied source factor `Q[D]`
determines whether the bound can be evaluated from the available experiments. -/
theorem partial_transport_bounds (source : Model n) {G : ADMG n}
    (conforming : source.scm.toMech.diag = G) {C C' D : Finset (Fin n)}
    (hCC' : C ⊆ C') (hC'D : C' ⊆ D) (ancestral : G.AncestralIn C' C)
    (v : ∀ i, source.X i) (targetFactor : ℝ) (invariant : targetFactor = source.scm.Q C v) :
    margSum (C' \ C) v (source.scm.Q D) ≤ targetFactor ∧
      targetFactor ≤ margSum (C' \ C) v
        (fun a => source.scm.Q D a + 1 - margSum C' a (source.scm.Q D)) := by
  have marginal := source.scm.Q_marg_ancestral conforming hCC' ancestral v
  rw [invariant, ← marginal]
  constructor
  · exact Finset.sum_le_sum (fun a _ => (nested_factor_bounds source hC'D a).1)
  · exact Finset.sum_le_sum (fun a _ => (nested_factor_bounds source hC'D a).2)

/-- Proposition 2 in its latent-projection form. A POMIS of the projection
away from non-manipulable vertices is an unconstrained MIS of the original
diagram, so its arms can enter the unconstrained upper-dominance comparison. -/
theorem projected_pomis_is_original_mis {G : ADMG n} (hG : G.WF)
    (removed : List (Fin n)) {y : Fin n} (hy : y ∉ removed) {X : Finset (Fin n)}
    (hX : POMIS (ConfDiag (Scb2019.project G removed)) y X) : MIS (ConfDiag G) y X :=
  ((Scb2019.constrained_pomis_iff_projected_pomis hG removed hy X).mpr hX).2.1

end OpenCausalScienceAnalysis.Scb2026Transport

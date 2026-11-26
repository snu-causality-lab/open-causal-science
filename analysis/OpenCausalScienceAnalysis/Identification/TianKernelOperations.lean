import OpenCausalScience.Papers.TianPearl2003.IdentifyCorrectness
import OpenCausalScience.Papers.TianPearl2003.IdentifyReachability
import OpenCausalScienceAnalysis.Identification.QFactor

/-!
# Tian's Identify plan with a finite SCM

The causal diagram supplies the directed and bidirected edges of the graph plan. A finite
structural causal model with independent roots supplies the causal factors. For a strictly
positive observational law, the execution uses ancestral marginal sums and products of
successive prefix ratios, as in R-290-L, Lemmas 3 and 4 and Figure 7.

Source: https://ftp.cs.ucla.edu/pub/stat_ser/R290-L.pdf
-/

namespace OpenCausalScienceAnalysis.TianPearl2003

open OpenCausalScience
open OpenCausalScience.Papers.TianPearl2003
open IdentifyRecurrence IdentifyReachability

variable {n : ℕ}

/-- An ADMG with its two edge classes encoded by endpoint marks. -/
def toMixedGraph (G : Mec.ADMG n) (wf : G.WF) : MixedGraph n where
  edge u a v b :=
    match a, b with
    | false, false => false
    | false, true => G.dir u v
    | true, false => G.dir v u
    | true, true => G.bi u v
  symmetric := by
    intro u a v b
    cases a <;> cases b <;> first | rfl | exact wf.2.2.1 u v
  loop_free := by
    intro u a b
    cases a <;> cases b <;> first | rfl | exact wf.1 u | exact wf.2.1 u
  no_arrow_of_undirected := by
    intro u v w mark h
    cases h

private theorem from_ancestors_subset (G : MixedGraph n) (H C : Vertices n) :
    (ancestors G H C).toFinset ⊆ H.toFinset := by
  intro v hv
  have h := (mem_ancestors_iff G H C v).mp (by simpa only [List.mem_toFinset] using hv)
  simpa only [List.mem_toFinset] using h.in_current

theorem ancestors_ancestralIn (G : Mec.ADMG n) (wf : G.WF) (H C : Vertices n) :
    G.AncestralIn H.toFinset (ancestors (toMixedGraph G wf) H C).toFinset := by
  intro a ha b hb hpath
  have inside : ∀ {p q}, Mec.Reach G.dir (Finset.univ \ H.toFinset) p q →
      p ∈ H.toFinset → q ∈ H.toFinset := by
    intro p q hr hp
    cases hr with
    | refl => exact hp
    | tail _ edge => simpa using edge.2
  revert hb
  induction hpath with
  | refl => exact id
  | @tail mid last path edge ih =>
    intro hb
    apply ih
    apply List.mem_toFinset.mpr
    apply ancestors_closed_under_parents (toMixedGraph G wf) H C edge.1
      (List.mem_toFinset.mp (inside path ha))
    exact List.mem_toFinset.mp hb

theorem district_eq_ccOf (G : Mec.ADMG n) (wf : G.WF) (H : Vertices n) {root : Fin n}
    (present : root ∈ H) :
    (district (toMixedGraph G wf) H root).toFinset = G.ccOf H.toFinset root := by
  ext v
  rw [List.mem_toFinset, mem_district_iff, Mec.ADMG.ccOf, ← Mec.reach_iff_mem_reachSet]
  constructor
  · intro reached
    induction reached with
    | @seed w _ wroot =>
      have eq : w = root := by simpa using wroot
      subst w
      exact Mec.Reach.refl root
    | step _ inH edge ih =>
      exact Mec.Reach.tail ih edge (by simpa using inH)
  · intro reached
    induction reached with
    | refl => exact .seed present (by simp)
    | tail _ edge ih =>
      exact .step ih (by simpa using edge.2) edge.1

private theorem district_empty (G : MixedGraph n) (H : Vertices n) {root : Fin n}
    (absent : root ∉ H) :
    (district G H root).toFinset = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have reached := (mem_district_iff G H root v).mp (List.mem_toFinset.mp hv)
  clear hv
  induction reached with
  | @seed w present wroot =>
    have eq : w = root := by simpa using wroot
    exact absent (eq ▸ present)
  | step _ _ _ ih => exact ih

/-- Sorting by structural rank supplies the order used in the prefix ratio formula. -/
noncomputable def rankOrder (rank : Fin n → ℕ) (H : Finset (Fin n)) : List (Fin n) :=
  H.toList.mergeSort fun a b => decide (rank a ≤ rank b)

theorem rankOrder_isTopoOrder (G : Mec.ADMG n) (rank : Fin n → ℕ)
    (increases : ∀ {a b}, G.dir a b = true → rank a < rank b) (H : Finset (Fin n)) :
    G.IsTopoOrder H (rankOrder rank H) := by
  let ord := rankOrder rank H
  have perm : ord.Perm H.toList := List.mergeSort_perm _ _
  have mem : ∀ v, v ∈ ord ↔ v ∈ H := fun v =>
    perm.mem_iff.trans Finset.mem_toList
  refine ⟨perm.nodup_iff.mpr H.nodup_toList, mem, ?_⟩
  intro a ha b hb edge
  have ranked : rank a < rank b := increases edge
  have ordered : ord.Pairwise (fun a b => rank a ≤ rank b) := by
    simpa only [ord, rankOrder, decide_eq_true_eq] using
      (List.pairwise_mergeSort
        (le := fun a b : Fin n => decide (rank a ≤ rank b))
        (fun a b c hab hbc => decide_eq_true (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
        (fun a b => Bool.or_eq_true_iff.mpr ((le_total (rank a) (rank b)).imp
          decide_eq_true decide_eq_true)) H.toList)
  have ha' := List.idxOf_lt_length_of_mem ((mem a).mpr ha)
  have hb' := List.idxOf_lt_length_of_mem ((mem b).mpr hb)
  apply Nat.lt_of_not_ge
  intro notBefore
  rcases Nat.lt_or_eq_of_le notBefore with after | same
  · have h := List.pairwise_iff_getElem.mp ordered _ _ hb' ha' after
    rw [List.getElem_idxOf hb', List.getElem_idxOf ha'] at h
    exact (not_lt_of_ge h) ranked
  · have equal := (List.getElem_idxOf hb').symm.trans
      ((getElem_congr rfl same hb').trans (List.getElem_idxOf ha'))
    exact (ne_of_lt ranked) (congrArg rank equal.symm)

section Execute

variable {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
variable [∀ i, Inhabited (X i)]
variable {L : Type} {U : L → Type} [Fintype L] [DecidableEq L] [∀ l, Fintype (U l)]
variable (M : Mec.SCM n X L U)

/-- The graph used by the Identify plan records the SCM's structural arguments and shared roots. -/
def modelGraph : MixedGraph n :=
  toMixedGraph M.toMech.diag M.toMech.diag_wf

/-- Interpret Identify's instructions as arithmetic on the SCM's finite causal factors.
Strict positivity of the observational assignment law supplies the support for the ratios. -/
noncomputable def kernelOperations (positive : ∀ v, 0 < M.Q Finset.univ v) :
    IdentifyCorrectness.KernelOperations (modelGraph M) ((∀ i, X i) → ℝ) where
  kernel H := M.Q H.toFinset
  marginalize H C P v := Mec.margSum (H.toFinset \ C.toFinset) v P
  extract H C := Mec.cfac (X := X) (rankOrder M.toMech.rank H.toFinset) H.toFinset C.toFinset
  extensional H C same := by
    have sets : H.toFinset = C.toFinset := by
      ext v
      simpa only [List.mem_toFinset] using same v
    exact congrArg M.Q sets
  marginalize_ancestors H C := by
    funext v
    exact M.Q_marg_ancestral rfl (from_ancestors_subset (modelGraph M) H C)
      (ancestors_ancestralIn M.toMech.diag M.toMech.diag_wf H C) v
  extract_district H root := by
    funext v
    by_cases present : root ∈ H
    · have ccomp : (district (modelGraph M) H root).toFinset ∈ M.toMech.diag.ccomps H.toFinset := by
        rw [modelGraph, district_eq_ccOf M.toMech.diag M.toMech.diag_wf H present]
        exact Mec.QFac.ccOf_mem_ccomps (List.mem_toFinset.mpr present)
      exact M.cfac_eq_Q_of_pos rfl ccomp
        (rankOrder_isTopoOrder M.toMech.diag M.toMech.rank
          (fun h => M.toMech.pa_rank (M.toMech.diag_dir.mp h)) H.toFinset)
        v (M.Q_pos_of_observational_pos H.toFinset v (positive v))
    · have empty := district_empty (modelGraph M) H present
      rw [empty, M.Q_empty v]
      simp [Mec.cfac]

/-- A successful execution of the Identify plan yields the target causal factor. -/
theorem successful_identify_eq_Q (positive : ∀ v, 0 < M.Q Finset.univ v)
    (target : Vertices n) (root : Fin n) (current : Vertices n) (value : (∀ i, X i) → ℝ)
    (successful : IdentifyCorrectness.run (kernelOperations M positive)
      (identifyPlan (modelGraph M) target root current) (M.Q current.toFinset) = some value) :
    value = M.Q target.toFinset :=
  IdentifyCorrectness.successful_plan_returns_target (kernelOperations M positive)
    target root current value successful

end Execute

end OpenCausalScienceAnalysis.TianPearl2003

module
public import OpenCausalScience.Graph.DirectedEdgeEdit
public import OpenCausalScience.Papers.AndrewsEtAl2023.PopulationProjection
public import OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

/-! # Decomposable scores for a backward deletion

A single arrow deletion changes one local-score term. Score equivalence
then transfers the same comparison between any representatives of the
before and after classes. -/

namespace OpenCausalScience.Papers.AndrewsEtAl2023.DeletionScore

open OpenCausalScience.Probability.CI
open GrowShrinkTree PopulationProjection
open VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat}

/-- Score equivalence is a separate assumption from local consistency. -/
def ScoreEquivalent (scores : Fin n → LocalScore n) : Prop :=
  ∀ G H : DAG n, SameDConnections G H → decomposableScore scores G = decomposableScore scores H

private def parentsOf (G : DAG n) (v : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun p => G.edge p v

private theorem sum_eq_of_perm {a b : List Rat} (same : a.Perm b) : a.sum = b.sum := by
  induction same with
  | nil => rfl
  | cons x _ ih => simp only [List.sum_cons, ih]
  | swap x y rest =>
    simp only [List.sum_cons]
    rw [← Rat.add_assoc, Rat.add_comm y x, Rat.add_assoc]
  | trans _ _ left right => exact left.trans right

private theorem parents_unchanged (G : DAG n) (u v z : Fin n) (unchanged : z ≠ v) :
    parentsOf (G.deleteArrow u v) z = parentsOf G z := by
  have eq : (fun p => (G.deleteArrow u v).edge p z) = (fun p => G.edge p z) := by
    funext p
    apply Bool.eq_iff_iff.mpr
    rw [G.deleteArrow_edge_iff]
    simp [unchanged]
  simp [parentsOf, eq]

private theorem parents_mask (G : DAG n) (v : Fin n) :
    maskOfList (parentsOf G v) = fun p => G.edge p v := by
  funext p
  apply Bool.eq_iff_iff.mpr
  simp [maskOfList, parentsOf]

private theorem parent_set_split (G : DAG n) (u v : Fin n) (present : G.edge u v = true) :
    maskOfList (parentsOf G v) = maskOfList (u :: parentsOf (G.deleteArrow u v) v) := by
  funext p
  apply Bool.eq_iff_iff.mpr
  simp only [maskOfList, parentsOf, decide_eq_true_eq, List.mem_cons, List.mem_filter, List.mem_finRange,
    true_and, DAG.deleteArrow_edge_iff]
  by_cases same : p = u
  · subst p
    simp [present]
  · simp [same]

private theorem score_compares_only_deleted_parent_row (scores : Fin n → LocalScore n) (G : DAG n)
    (u v : Fin n) :
    (decomposableScore scores G < decomposableScore scores (G.deleteArrow u v)) ↔
      scores v (parentsOf G v) < scores v (parentsOf (G.deleteArrow u v) v) := by
  let other := (List.finRange n).erase v
  have split : (List.finRange n).Perm (v :: other) := List.perm_cons_erase (List.mem_finRange v)
  have sumSplit (H : DAG n) : decomposableScore scores H =
      scores v (parentsOf H v) + (other.map (fun z => scores z (parentsOf H z))).sum := by
    exact sum_eq_of_perm (split.map fun z => scores z (parentsOf H z))
  rw [sumSplit G, sumSplit (G.deleteArrow u v)]
  have sameOther : other.map (fun z => scores z (parentsOf (G.deleteArrow u v) z)) =
      other.map (fun z => scores z (parentsOf G z)) := by
    apply List.map_congr_left
    intro z hz
    have ⟨untouched, _⟩ :=
      List.nodup_cons.mp (split.nodup_iff.mp (List.nodup_finRange n))
    have different : z ≠ v := by
      intro same
      subst z
      exact untouched hz
    rw [parents_unchanged G u v z different]
  rw [sameOther, Rat.add_lt_add_right]

/-- Under local consistency, deleting an existing arrow strictly improves
the decomposable score exactly when the former parent is independent of the
child given its remaining parents. -/
theorem deletion_gain_iff_parent_independence {J : Relation n} {scores : Fin n → LocalScore n}
    (G : DAG n) {u v : Fin n} (present : G.edge u v = true)
    (localScore : LocallyConsistent J v (scores v)) :
    (decomposableScore scores G < decomposableScore scores (G.deleteArrow u v)) ↔
      J (single v) (single u) (fun p => (G.deleteArrow u v).edge p v) := by
  let P := parentsOf (G.deleteArrow u v) v
  have maskEq : maskOfList P = fun p => (G.deleteArrow u v).edge p v := parents_mask _ _
  have existing := localScore.set_score (parent_set_split G u v present)
  have distinct : u ≠ v := by
    intro same
    subst u
    exact G.no_directed_cycle v (.single present)
  have notParent : u ∉ P := by
    intro h
    have deleted := (G.deleteArrow_edge_iff u v u v).mp (List.mem_filter.mp h).2
    exact deleted.2 ⟨rfl, rfl⟩
  have notChild : v ∉ P := by
    intro h
    have loop := (List.mem_filter.mp h).2
    exact (G.deleteArrow u v).no_directed_cycle v (.single loop)
  rw [score_compares_only_deleted_parent_row scores G u v, existing, ← maskEq]
  constructor
  · intro improves
    apply Classical.byContradiction
    intro dependent
    exact (Rat.not_lt.mpr (Rat.le_of_lt (localScore.gain distinct notParent notChild dependent))) improves
  · exact localScore.loss distinct notParent notChild

/-- When the score is equivalent across DAG representatives, the same strict
gain criterion applies to any representatives of the before and after MECs. -/
theorem representative_deletion_gain_iff {J : Relation n} {scores : Fin n → LocalScore n}
    (equivalentScore : ScoreEquivalent scores) {G start finish : DAG n} {u v : Fin n}
    (present : G.edge u v = true) (localScore : LocallyConsistent J v (scores v))
    (before : SameDConnections G start) (after : SameDConnections (G.deleteArrow u v) finish) :
    (decomposableScore scores start < decomposableScore scores finish) ↔
      J (single v) (single u) (fun p => (G.deleteArrow u v).edge p v) := by
  rw [← equivalentScore _ _ before, ← equivalentScore _ _ after]
  exact deletion_gain_iff_parent_independence G present localScore

end

end OpenCausalScience.Papers.AndrewsEtAl2023.DeletionScore

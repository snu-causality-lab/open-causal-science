module
public import OpenCausalScience.Papers.LamEtAl2022.TSPCorrespondence
public import OpenCausalScience.Papers.Chickering2002.DeletionIndependence
public import OpenCausalScience.Papers.AndrewsEtAl2023.DeletionScore

/-! # The score of a covered tuck

With score equivalence and strict local score consistency, an equal-size
covered tuck ties, and a covered tuck deleting arrows strictly improves.
The result connects the edge-count and grow–shrink scores for each covered
candidate in the compositional graphoid regime. -/

namespace OpenCausalScience.Papers.LamEtAl2022

open Discovery Probability.CI RaskuttiUhler2018 Chickering2002
open Chickering1995.Transformation
open VermaPearl1990.Equivalence
open AndrewsEtAl2023.GrowShrinkTree AndrewsEtAl2023.PopulationProjection AndrewsEtAl2023.DeletionScore

@[expose] public section

variable {n : Nat}

theorem backward_score_monotone {J : Relation n} {independent : CIOracle n}
    {scores : Fin n → LocalScore n} (g : Graphoid J) (agrees : MatchesOracle J independent)
    (localScore : ∀ child, LocallyConsistent J child (scores child)) (equivScore : ScoreEquivalent scores)
    {G H : DAG n} (trajectory : BackwardSequence H G) (target : IsMarkov H independent) :
    (decomposableScore scores G ≤ decomposableScore scores H) ∧
      (arrowCount H < arrowCount G → decomposableScore scores G < decomposableScore scores H) := by
  induction trajectory with
  | @done current same =>
    have sameScore := equivScore _ _ (same_dConnections_of_edge_eq same)
    refine ⟨by rw [sameScore]; exact Rat.le_refl, ?_⟩
    intro fewer
    have sameCount : arrowCount current = arrowCount H := by simp [arrowCount, same]
    omega
  | reverse rev _ ih =>
    have sameScore := equivScore _ _ (sameDConnections_of_reversal rev)
    rw [sameScore, arrow_count_eq_of_reversal rev]
    exact ih
  | @delete current a b edge rest ih =>
    have before := markov_of_separation_subset (.of_edge_subset
      (fun x y e => ((current.deleteArrow_edge_iff a b x y).mp e).1))
      (markov_of_separation_subset rest.implies_map target)
    have after := markov_of_separation_subset rest.implies_map target
    have test := (deletion_markov_iff_parent_independence g agrees before edge).mp after
    have gain := (deletion_gain_iff_parent_independence current edge (localScore b)).mpr test
    have rises : decomposableScore scores current < decomposableScore scores H :=
      Rat.not_le.mp (fun wrong => Rat.not_le.mpr gain (Rat.le_trans ih.1 wrong))
    exact ⟨Rat.le_of_lt rises, fun _ => rises⟩

/-- Comparison of the grow–shrink score for a covered tuck and its original
order. These are exactly the strict and tie tests used by covered DFS. -/
theorem covered_tuck_score_comparisons {J : Relation n} {independent : CIOracle n}
    {scores : Fin n → LocalScore n} (g : Graphoid J) (compose : Composition J)
    (agrees : MatchesOracle J independent) (localScore : ∀ child, LocallyConsistent J child (scores child))
    (equivScore : ScoreEquivalent scores) {start next : List (Fin n)} (valid : VertexOrder start)
    (candidate : next ∈ moves independent .covered start) :
    let score := AndrewsEtAl2023.OrderSearch.score scores
    let before := arrowCount (graph independent start)
    let after := arrowCount (graph independent next)
    (score start < score next ↔ after < before) ∧ (score start = score next ↔ after = before) := by
  dsimp only
  have oldMarkov := induced_order_is_markov g agrees start.idxOf valid.idx_unique
  have nextValid := valid.of_perm (moves_perm candidate)
  have newMarkov := induced_order_is_markov g agrees next.idxOf nextValid.idx_unique
  obtain ⟨H, a, b, rev, sub⟩ := covered_tuck_reversal_then_subset valid candidate oldMarkov
  let G := graph independent start
  let K := graph independent next
  have countH : arrowCount G = arrowCount H := arrow_count_eq_of_reversal rev
  have le : arrowCount K ≤ arrowCount G := by
    rw [countH]
    exact arrow_count_le_of_subset sub
  have sameScore : decomposableScore scores G = decomposableScore scores H :=
    equivScore _ _ (sameDConnections_of_reversal rev)
  have gain : arrowCount K < arrowCount G → decomposableScore scores G < decomposableScore scores K := by
    intro less
    rw [sameScore]
    apply (backward_score_monotone g agrees localScore equivScore (backward_sequence_of_edge_subset sub) newMarkov).2
    rwa [← countH]
  have equal : arrowCount K = arrowCount G → decomposableScore scores G = decomposableScore scores K := by
    intro count
    exact sameScore.trans (equivScore _ _ (same_dConnections_of_edge_eq
      (edge_eq_of_subset_of_arrow_count_eq sub (count.trans countH)).symm))
  rw [order_score_eq_induced_score g compose localScore agrees,
    order_score_eq_induced_score g compose localScore agrees]
  change (decomposableScore scores G < decomposableScore scores K ↔ arrowCount K < arrowCount G) ∧
    (decomposableScore scores G = decomposableScore scores K ↔ arrowCount K = arrowCount G)
  refine ⟨⟨?_, gain⟩, ⟨?_, equal⟩⟩
  · intro higher
    by_cases count : arrowCount K = arrowCount G
    · rw [equal count] at higher
      exact (Rat.lt_irrefl higher).elim
    · exact Nat.lt_of_le_of_ne le count
  · intro same
    by_cases count : arrowCount K = arrowCount G
    · exact count
    · have higher := gain (Nat.lt_of_le_of_ne le count)
      rw [same] at higher
      exact (Rat.lt_irrefl higher).elim

end

end OpenCausalScience.Papers.LamEtAl2022

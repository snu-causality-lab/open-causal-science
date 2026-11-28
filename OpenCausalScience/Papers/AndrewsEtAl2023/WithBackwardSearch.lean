module
public import OpenCausalScience.Papers.Chickering2002.InclusionTransformation
public import OpenCausalScience.Papers.AndrewsEtAl2023.DeletionScore
public import OpenCausalScience.Papers.AndrewsEtAl2023.SampleScoreSigns
public import OpenCausalScience.Papers.Chickering2002.DeletionIndependence
public import OpenCausalScience.Papers.Chickering2002.BackwardSearch

/-! # The BOSS and BES argument in Proposition 2

The proposition is stated at the score-comparison level. The theorem
uses the general DAG inclusion transformation and treats statistical score
conditions as separate inputs.
-/

namespace OpenCausalScience.Papers.AndrewsEtAl2023

open Discovery Probability Probability.CI Chickering2002 PopulationProjection DeletionScore GrowShrinkTree
open Discovery.FiniteCIQueries SampleScoreSigns
open VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat}

theorem decomposable_deletion_score_consistent {truth : DAG n} {J : Relation n}
    (g : Graphoid J) (agrees : MatchesOracle J (graphOracle truth))
    {scores : Fin n → LocalScore n} (localScore : ∀ child, LocallyConsistent J child (scores child))
    (equivalent : ScoreEquivalent scores) :
    DeletionScoreConsistent truth (decomposableScore scores) where
  equivalent := equivalent
  gain_iff G _u v edge contains :=
    (deletion_gain_iff_parent_independence G edge (localScore v)).trans
      (deletion_markov_iff_parent_independence g agrees contains edge).symm

/-- The order phase is followed by a search over the deletion neighborhood
of each current Markov equivalence class. -/
noncomputable def withBackwardSearch (scores : Fin n → LocalScore n)
    (initial : List (Fin n)) : DAG n :=
  (backwardSearch (decomposableScore scores) (OrderSearch.selectedDAG scores initial)).val

/-- Proposition 2's graphical and score argument. Strict local score signs
and score equivalence suffice under DAG faithfulness. -/
theorem boss_bes_recovers_dConnections {truth : DAG n} {J : Relation n}
    (sg : Semigraphoid J) (faithful : DAGFaithful truth J)
    {scores : Fin n → LocalScore n} (localScore : ∀ child, LocallyConsistent J child (scores child))
    (equivalent : ScoreEquivalent scores) (initial : List (Fin n)) (complete : ∀ v, v ∈ initial) :
    SameDConnections (withBackwardSearch scores initial) truth := by
  have contains := (selected_dag_sgs_minimal_of_faithful sg faithful localScore initial complete).1
  have consistent := decomposable_deletion_score_consistent (faithful_graphoid faithful sg)
    (graph_oracle_matches_faithful faithful) localScore equivalent
  exact backward_search_is_perfect (inclusion_transformation n) consistent contains

/-- The in-probability conclusion from the finite local-score comparison
library. The sampling law supplies the per-comparison error bounds. -/
theorem boss_bes_sample_failure_vanishes {truth : DAG n} {J : Relation n} {Ω : Nat → Type}
    (sg : Semigraphoid J) (faithful : DAGFaithful truth J)
    (law : ∀ m, FiniteLaw (Ω m)) (scores : ∀ m, Ω m → Fin n → LocalScore n)
    (setScores : ∀ m a, SetScores (scores m a)) (equivalent : ∀ m a, ScoreEquivalent (scores m a))
    (initial : ∀ m, Ω m → List (Fin n)) (complete : ∀ m a v, v ∈ initial m a)
    (each : ∀ q ∈ comparisons n, ∀ ε : Rat, 0 < ε → ∃ N, ∀ m, N ≤ m →
      (law m).mass (fun a => comparisonError J (scores m a) q) < ε) :
    ∀ ε : Rat, 0 < ε → ∃ N, ∀ m, N ≤ m → (law m).mass
      (fun a => @decide (¬ SameDConnections (withBackwardSearch (scores m a) (initial m a)) truth)
        (Classical.propDecidable _)) < ε := by
  classical
  apply sample_failure_vanishes_of_fixed_signs law scores _ setScores _ each
  intro m a localScore
  simp [boss_bes_recovers_dConnections sg faithful localScore (equivalent m a) _ (complete m a)]

end

end OpenCausalScience.Papers.AndrewsEtAl2023

module
public import OpenCausalScience.Papers.Chickering2002.InclusionTransformation
public import OpenCausalScience.Papers.LamEtAl2022.ScoreComparison
public import OpenCausalScience.Papers.LamEtAl2022.GraphoidCorrectness
public import OpenCausalScience.Papers.AndrewsEtAl2023.SampleScoreSigns

/-! # Grow–shrink scored GRaSP

The search uses comparisons of the grow–shrink scores. A natural-number
rank on the finite collection of complete orders preserves the strict
and equal comparisons used by the DFS. -/

namespace OpenCausalScience.Papers.LamEtAl2022

open Discovery Probability Probability.CI FiniteCIQueries
open RaskuttiUhler2018 Chickering2002 VermaPearl1990.DAGEquivalence
open AndrewsEtAl2023.GrowShrinkTree AndrewsEtAl2023.PopulationProjection
open AndrewsEtAl2023.DeletionScore AndrewsEtAl2023.SampleScoreSigns

@[expose] public section

variable {n : Nat}

def scoredMoves (scores : Fin n → LocalScore n) (tier : Tier) (order : List (Fin n)) :
    List (List (Fin n)) :=
  (vertexPairs n).filterMap fun (j, k) => move tier (project scores order.idxOf) order j k

def scoredGraphKey (scores : Fin n → LocalScore n) (order : List (Fin n)) : List (Fin n × Fin n) :=
  edgeKey (project scores order.idxOf)

def scoreRank (scores : Fin n → LocalScore n) (order : List (Fin n)) : Nat :=
  AndrewsEtAl2023.BestMove.higherScoreCount
    (AndrewsEtAl2023.OrderSearch.score scores) order (allOrders n)

private theorem order_mem_all_orders {order : List (Fin n)} (valid : VertexOrder order) :
    order ∈ allOrders n := by
  apply mem_permutations_iff.mpr
  apply List.perm_iff_count.mpr
  intro v
  rw [valid.nodup.count, (List.nodup_finRange n).count]
  simp [valid.covers v]

private theorem score_rank_drops {scores : Fin n → LocalScore n} {before after : List (Fin n)}
    (valid : VertexOrder after)
    (better : AndrewsEtAl2023.OrderSearch.score scores before < AndrewsEtAl2023.OrderSearch.score scores after) :
    scoreRank scores after < scoreRank scores before :=
  AndrewsEtAl2023.BestMove.higher_score_count_lt better (order_mem_all_orders valid)

def scoredImprove (scores : Fin n → LocalScore n) (tier : Tier) (depth : Nat) (order : List (Fin n)) :
    List (Fin n) :=
  Search.descend (scoredMoves scores tier) (scoreRank scores) (scoredGraphKey scores) depth order

/-- The three-tier control flow with the order score from grow–shrink. -/
def scoredSearch (scores : Fin n → LocalScore n) (depth : Nat) (tier : Tier) (order : List (Fin n)) :
    List (Fin n) :=
  let covered := scoredImprove scores .covered depth order
  match tier with
  | .covered => covered
  | .singular => scoredImprove scores .singular depth covered
  | .all => scoredImprove scores .all depth (scoredImprove scores .singular depth covered)

private theorem scored_moves_eq_moves {J : Relation n} {independent : CIOracle n}
    {scores : Fin n → LocalScore n} (g : Graphoid J) (comp : Composition J)
    (agrees : MatchesOracle J independent) (localScore : ∀ child, LocallyConsistent J child (scores child))
    (tier : Tier) : scoredMoves scores tier = moves independent tier := by
  funext order
  simp only [scoredMoves, moves, graph, project_eq_orderDAG g comp localScore agrees]

private theorem scored_keys_eq_graph_keys {J : Relation n} {independent : CIOracle n}
    {scores : Fin n → LocalScore n} (g : Graphoid J) (comp : Composition J)
    (agrees : MatchesOracle J independent) (localScore : ∀ child, LocallyConsistent J child (scores child)) :
    scoredGraphKey scores = graphKey independent := by
  funext order
  rw [scoredGraphKey, project_eq_orderDAG g comp localScore agrees, graphKey_eq_edgeKey]
  rfl

private theorem improvement_under_score {J : Relation n} {independent : CIOracle n}
    {scores : Fin n → LocalScore n} (g : Graphoid J) (comp : Composition J)
    (agrees : MatchesOracle J independent) (localScore : ∀ child, LocallyConsistent J child (scores child))
    (equivScore : ScoreEquivalent scores) {start target : List (Fin n)} {depth seen}
    (path : Search.Improvement (moves independent .covered) (fun order => (graphKey independent order).length)
      (graphKey independent) depth seen start target) (valid : VertexOrder start) :
    Search.Improvement (scoredMoves scores .covered) (scoreRank scores) (scoredGraphKey scores)
      depth seen start target := by
  rw [scored_moves_eq_moves g comp agrees localScore, scored_keys_eq_graph_keys g comp agrees localScore]
  induction path with
  | direct candidate fresh lower =>
    have compares := covered_tuck_score_comparisons g comp agrees localScore equivScore valid candidate
    have better := compares.1.mpr (by simpa only [graphKey_length] using lower)
    exact .direct candidate fresh (score_rank_drops (valid.of_perm (moves_perm candidate)) better)
  | @plateau depth seen start next _ candidate fresh tie _ ih =>
    have compares := covered_tuck_score_comparisons g comp agrees localScore equivScore valid candidate
    have same := compares.2.mpr (by simpa only [graphKey_length] using tie)
    have rankTie : scoreRank scores next = scoreRank scores start := by
      unfold scoreRank AndrewsEtAl2023.BestMove.higherScoreCount
      rw [same]
    exact .plateau candidate fresh rankTie (ih (valid.of_perm (moves_perm candidate)))

private theorem scored_improve_complete_and_nondecreasing {J : Relation n} {independent : CIOracle n}
    {scores : Fin n → LocalScore n} (g : Graphoid J) (comp : Composition J)
    (agrees : MatchesOracle J independent) (localScore : ∀ child, LocallyConsistent J child (scores child))
    (depth : Nat) (tier : Tier) {order : List (Fin n)} (valid : VertexOrder order) :
    VertexOrder (scoredImprove scores tier depth order) ∧
      AndrewsEtAl2023.OrderSearch.score scores order ≤
        AndrewsEtAl2023.OrderSearch.score scores (scoredImprove scores tier depth order) := by
  have unchanged := Search.descend_perm (scoredMoves scores tier) (scoreRank scores) (scoredGraphKey scores)
    depth order (fun {start next} candidate => moves_perm
      (by rw [← scored_moves_eq_moves g comp agrees localScore]; exact candidate : next ∈ moves independent tier start))
  refine ⟨valid.of_perm unchanged, Rat.not_lt.mp ?_⟩
  intro worse
  have rankBetter := score_rank_drops valid worse
  exact (Nat.not_lt_of_ge (Search.descend_spec _ _ _ _ _).1) rankBetter

/-- The scored covered search has the same P-minimality guarantee as the
oracle search under the mathematical conditions used by the two scores. -/
theorem scored_covered_search_pminimal {J : Relation n} {independent : CIOracle n}
    {scores : Fin n → LocalScore n}
    (g : Graphoid J) (comp : Composition J) (agrees : MatchesOracle J independent)
    (localScore : ∀ child, LocallyConsistent J child (scores child)) (equivScore : ScoreEquivalent scores)
    {initial : List (Fin n)} (valid : VertexOrder initial) {depth : Nat}
    (deep : (allOrders n).length ≤ depth) :
    PMinimal independent (graph independent (scoredSearch scores depth .covered initial)) := by
  let order := scoredSearch scores depth .covered initial
  have complete := (scored_improve_complete_and_nondecreasing g comp agrees localScore depth .covered valid).1
  apply Classical.byContradiction
  intro failed
  obtain ⟨next, route⟩ := improvement_of_not_pminimal (inclusion_transformation n)
    (fun π complete => induced_order_is_markov g agrees π.idxOf complete.idx_unique) (order := order)
    complete failed deep
  have noPath := (Search.descend_spec (scoredMoves scores .covered) (scoreRank scores)
    (scoredGraphKey scores) depth initial).2
  have improved := improvement_under_score g comp agrees localScore equivScore route complete
  rw [← scored_keys_eq_graph_keys g comp agrees localScore] at improved
  exact (Search.no_first_improvement_iff.mp noPath) next improved

private theorem scored_search_preserves_order_and_score {J : Relation n} {independent : CIOracle n}
    {scores : Fin n → LocalScore n} (g : Graphoid J) (comp : Composition J)
    (agrees : MatchesOracle J independent) (localScore : ∀ child, LocallyConsistent J child (scores child))
    (depth : Nat) (tier : Tier) {initial : List (Fin n)} (valid : VertexOrder initial) :
    VertexOrder (scoredSearch scores depth tier initial) ∧
      AndrewsEtAl2023.OrderSearch.score scores (scoredSearch scores depth .covered initial) ≤
        AndrewsEtAl2023.OrderSearch.score scores (scoredSearch scores depth tier initial) := by
  let c := scoredSearch scores depth .covered initial
  have covered := (scored_improve_complete_and_nondecreasing g comp agrees localScore depth .covered valid).1
  change VertexOrder c at covered
  cases tier with
  | covered => exact ⟨covered, Rat.le_refl⟩
  | singular => exact scored_improve_complete_and_nondecreasing g comp agrees localScore depth .singular covered
  | all =>
    have singular := scored_improve_complete_and_nondecreasing g comp agrees localScore depth .singular covered
    have full := scored_improve_complete_and_nondecreasing g comp agrees localScore depth .all singular.1
    exact ⟨full.1, Rat.le_trans singular.2 full.2⟩

def scoredDAG (scores : Fin n → LocalScore n) (depth : Nat) (tier : Tier) (initial : List (Fin n)) : DAG n :=
  project scores (scoredSearch scores depth tier initial).idxOf

/-- With consistent local signs and score equivalence, the actual scored
GRaSP algorithm recovers the population MEC for every tier. -/
theorem scored_grasp_recovers_mec {J : Relation n} {truth : DAG n}
    (sg : Semigraphoid J) (faithful : DAGFaithful truth J)
    {scores : Fin n → LocalScore n} (localScore : ∀ child, LocallyConsistent J child (scores child))
    (equivScore : ScoreEquivalent scores) {initial : List (Fin n)} (valid : VertexOrder initial)
    (tier : Tier) {depth : Nat} (deep : (allOrders n).length ≤ depth) :
    SameDConnections (scoredDAG scores depth tier initial) truth := by
  let independent := graphOracle truth
  have agrees : MatchesOracle J independent := graph_oracle_matches_faithful faithful
  have g := faithful_graphoid faithful sg
  have comp : Composition J := faithful_composition faithful
  let c := scoredSearch scores depth .covered initial
  let order := scoredSearch scores depth tier initial
  let C := graph independent c
  let H := graph independent order
  have minCovered := scored_covered_search_pminimal g comp agrees localScore equivScore valid deep
  have coverMec := IndependenceMap.same_dConnections
    (minCovered.2 truth (IndependenceMap.refl truth) minCovered.1) minCovered.1
  have properties := scored_search_preserves_order_and_score g comp agrees localScore depth tier valid
  have imap : IndependenceMap truth H := induced_order_is_markov g agrees order.idxOf properties.1.idx_unique
  have lowerBound : decomposableScore scores truth ≤ decomposableScore scores H := by
    have sameScore := equivScore _ _ coverMec
    change decomposableScore scores C = decomposableScore scores truth at sameScore
    rw [← sameScore]
    have pair := properties.2
    change AndrewsEtAl2023.OrderSearch.score scores c ≤ AndrewsEtAl2023.OrderSearch.score scores order at pair
    rwa [order_score_eq_induced_score g comp localScore agrees,
      order_score_eq_induced_score g comp localScore agrees] at pair
  have afterMec : SameDConnections H truth := by
    classical
    by_cases reverse : IndependenceMap H truth
    · exact IndependenceMap.same_dConnections reverse imap
    · have path := inclusion_transformation n truth H imap
      have fewer := backward_sequence_strict_arrow_count path reverse
      have lower := (backward_score_monotone g agrees localScore equivScore path
        (IndependenceMap.refl truth)).2 fewer
      exact (Rat.not_lt.mpr lowerBound lower).elim
  rw [scoredDAG, project_eq_orderDAG g comp localScore agrees]
  exact afterMec

/-- Per-comparison score sign convergence transfers to the finite scored
GRaSP algorithm, for any choice of starting order and tier. -/
theorem scored_grasp_sample_failure_vanishes {J : Relation n} {truth : DAG n} {Ω : Nat → Type}
    (sg : Semigraphoid J) (faithful : DAGFaithful truth J)
    (law : ∀ m, FiniteLaw (Ω m)) (scores : ∀ m, Ω m → Fin n → LocalScore n)
    (setScores : ∀ m a, SetScores (scores m a)) (equivalent : ∀ m a, ScoreEquivalent (scores m a))
    (initial : ∀ m, Ω m → List (Fin n)) (valid : ∀ m a, VertexOrder (initial m a))
    (tier : Tier) {depth : Nat} (deep : (allOrders n).length ≤ depth)
    (each : ∀ q ∈ comparisons n, ∀ ε : Rat, 0 < ε → ∃ N, ∀ m, N ≤ m →
      (law m).mass (fun a => comparisonError J (scores m a) q) < ε) :
    ∀ ε : Rat, 0 < ε → ∃ N, ∀ m, N ≤ m → (law m).mass
      (fun a => @decide (¬ SameDConnections (scoredDAG (scores m a) depth tier (initial m a)) truth)
        (Classical.propDecidable _)) < ε := by
  classical
  apply sample_failure_vanishes_of_fixed_signs law scores _ setScores _ each
  intro m a signs
  simp [scored_grasp_recovers_mec sg faithful signs (equivalent m a) (valid m a) tier deep]

end

end OpenCausalScience.Papers.LamEtAl2022

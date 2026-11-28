module
public import OpenCausalScience.Papers.Chickering2002.InclusionTransformation
public import OpenCausalScience.Papers.LamEtAl2022.OracleCorrectness
public import OpenCausalScience.Discovery.DAGGraphoid
public import OpenCausalScience.Discovery.OrderedMarkov
public import OpenCausalScience.Discovery.OracleConsistency

/-! # GRaSP under the graphoid and faithfulness assumptions

The finite oracle proofs use Chickering's inclusion transformation and
Markovness of order-induced DAGs. The latter follows from the shared
recursive-basis theorem. The sample result transfers finite CI error
bounds to this oracle procedure. -/

namespace OpenCausalScience.Papers.LamEtAl2022

open Discovery Probability Probability.CI FiniteCIQueries
open Chickering2002 RaskuttiUhler2018 VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat}

private theorem markov_orders_of_graphoid {J : Relation n} {independent : CIOracle n}
    (g : Graphoid J) (agrees : MatchesOracle J independent) :
    ∀ order, VertexOrder order → IsMarkov (graph independent order) independent :=
  fun order valid => induced_order_is_markov g agrees order.idxOf valid.idx_unique

/-- Theorem 4.5 under the finite graphoid axioms. -/
theorem exists_ct_sequence_of_graphoid {J : Relation n} {independent : CIOracle n}
    (g : Graphoid J) (agrees : MatchesOracle J independent)
    (initial : List (Fin n)) (valid : VertexOrder initial) :
    ∃ walk final, CtSequence independent initial walk final ∧
      PMinimal independent (graph independent final) := by
  obtain ⟨walk, final, seq, _, minimal⟩ := exists_ct_sequence_to_pminimal (inclusion_transformation n)
    (markov_orders_of_graphoid g agrees) initial valid
  exact ⟨walk, final, seq, minimal⟩

/-- With sufficient depth, GRaSP0 returns a P-minimal DAG for a graphoid. -/
theorem covered_search_pminimal_of_graphoid {J : Relation n} {independent : CIOracle n}
    (g : Graphoid J) (agrees : MatchesOracle J independent)
    {initial : List (Fin n)} (valid : VertexOrder initial)
    {depth : Nat} (deep : (allOrders n).length ≤ depth) :
    PMinimal independent (graph independent (search independent depth .covered initial)) :=
  covered_search_pminimal (inclusion_transformation n) (markov_orders_of_graphoid g agrees) valid deep

/-- The population part of Corollary 4.6 for any of the three tiers. -/
theorem grasp_recovers_mec_of_dag_faithful {J : Relation n} {independent : CIOracle n} {truth : DAG n}
    (sg : Semigraphoid J)
    (faithful : DAGFaithful truth J) (agrees : MatchesOracle J independent)
    (initial : List (Fin n)) (valid : VertexOrder initial) (tier : Tier)
    {depth : Nat} (deep : (allOrders n).length ≤ depth) :
    SameDConnections (graph independent (search independent depth tier initial)) truth := by
  have eq : FaithfulTo independent truth := fun x y c distinct left right =>
    (agrees x y c distinct left right).trans
      ((graph_oracle_matches_faithful faithful) x y c distinct left right).symm
  obtain ⟨forward, backward⟩ := search_recovers_mec_of_faithful (inclusion_transformation n)
    (markov_orders_of_graphoid (faithful_graphoid faithful sg) agrees) eq initial valid tier deep
  exact IndependenceMap.same_dConnections backward forward

/-- Pointwise CI query error tending to zero implies pointwise MEC recovery
in probability for the finite-oracle version of GRaSP. -/
theorem grasp_sample_oracle_error_vanishes {J : Relation n} {truth : DAG n} {Ω : Nat → Type}
    (law : ∀ m, FiniteLaw (Ω m)) (observed : ∀ m, Ω m → CIOracle n) (exact : CIOracle n)
    (sg : Semigraphoid J)
    (faithful : DAGFaithful truth J) (agrees : MatchesOracle J exact)
    (initial : List (Fin n)) (valid : VertexOrder initial) (tier : Tier)
    {depth : Nat} (deep : (allOrders n).length ≤ depth)
    (each : ∀ q ∈ comparisons n, ∀ ε : Rat, 0 < ε → ∃ N, ∀ m, N ≤ m →
      (law m).mass (fun a => oracleError (observed m a) exact q) < ε) :
    ∀ ε : Rat, 0 < ε → ∃ N, ∀ m, N ≤ m →
      (law m).mass (fun a =>
        @decide (¬ SameDConnections
          (graph (observed m a) (search (observed m a) depth tier initial)) truth)
          (Classical.propDecidable _)) < ε :=
  sample_oracle_error_vanishes law observed exact
    (fun independent => graph independent (search independent depth tier initial))
    (fun result => SameDConnections result truth)
    (grasp_recovers_mec_of_dag_faithful sg faithful agrees initial valid tier deep) each

end

end OpenCausalScience.Papers.LamEtAl2022

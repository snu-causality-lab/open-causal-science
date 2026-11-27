module
public import OpenCausalScience.Discovery.OrderDAG

/-! # Sparsest permutation: the ordered DAG and its necessary arrows

[Raskutti and Uhler (2018), Section 2](https://doi.org/10.1002/sta4.183).
The Markov relation uses the same executable d-separation semantics as the
ancestral moral search. -/

namespace OpenCausalScience.Papers.RaskuttiUhler2018

open OpenCausalScience.Discovery

@[expose] public section

variable {n : Nat}

/-- Every graphical separation is a conditional independence in the oracle. -/
def IsMarkov (G : DAG n) (independent : CIOracle n) : Prop :=
  ∀ x y condition, x ≠ y → condition x = false → condition y = false →
    graphOracle G x y condition = true → independent x y condition = true

/-- Every adjacent pair is dependent given each set excluding the endpoints. -/
def AdjacencyFaithful (G : DAG n) (independent : CIOracle n) : Prop :=
  ∀ x y condition, condition x = false → condition y = false →
    (G.edge x y = true ∨ G.edge y x = true) → independent x y condition = false

/-- A Markov graph respecting an order must include every arrow selected by
that order's CI tests. -/
theorem orderDAG_subgraph_of_markov {G : DAG n} {independent : CIOracle n}
    (order : Fin n → Nat) (uniqueRank : ∀ x y, order x = order y → x = y)
    (topological : ∀ x y, G.edge x y = true → order x < order y)
    (markov : IsMarkov G independent) {u v : Fin n}
    (edge : (orderDAG order independent).edge u v = true) : G.edge u v = true := by
  obtain ⟨earlier, dependent⟩ := (orderDAG_edge_iff _ _ _ _).mp edge
  cases arrow : G.edge u v with
  | true => rfl
  | false =>
    have distinct : v ≠ u := fun equal => (Nat.ne_of_lt earlier) (congrArg order equal.symm)
    have graphIndependent := graphOracle_predecessors_eq_not_edge order uniqueRank topological earlier
    rw [arrow] at graphIndependent
    have statisticalIndependent := markov v u _ distinct
      (by simp [predecessorsExcept]) (by simp [predecessorsExcept]) graphIndependent
    exact (Bool.false_ne_true (dependent.symm.trans statisticalIndependent)).elim

/-- A proper edge subset of the order-induced DAG cannot satisfy the Markov
condition for the same oracle. This is the minimality implication in the
proof of Lemma 2.1 of the authors' manuscript. -/
theorem markov_subgraph_edges_eq {H : DAG n} {independent : CIOracle n}
    (order : Fin n → Nat) (uniqueRank : ∀ x y, order x = order y → x = y)
    (subgraph : ∀ x y, H.edge x y = true → (orderDAG order independent).edge x y = true)
    (markov : IsMarkov H independent) : H.edge = (orderDAG order independent).edge := by
  have topological : ∀ x y, H.edge x y = true → order x < order y :=
    fun x y edge => ((orderDAG_edge_iff _ _ _ _).mp (subgraph x y edge)).1
  funext u v
  exact Bool.eq_iff_iff.mpr ⟨subgraph u v, orderDAG_subgraph_of_markov order uniqueRank topological markov⟩

/-- Markovness and adjacency faithfulness recover exactly the original DAG
when the supplied order is topological. -/
theorem orderDAG_recovers_of_adjacencyFaithful {G : DAG n} {independent : CIOracle n}
    (order : Fin n → Nat) (uniqueRank : ∀ x y, order x = order y → x = y)
    (topological : ∀ x y, G.edge x y = true → order x < order y)
    (markov : IsMarkov G independent) (faithful : AdjacencyFaithful G independent) :
    (orderDAG order independent).edge = G.edge := by
  funext u v
  apply Bool.eq_iff_iff.mpr
  refine ⟨orderDAG_subgraph_of_markov order uniqueRank topological markov, ?_⟩
  intro edge
  rw [orderDAG_edge_iff]
  exact ⟨topological _ _ edge, faithful v u _
    (by simp [predecessorsExcept]) (by simp [predecessorsExcept]) (.inr edge)⟩

end

end OpenCausalScience.Papers.RaskuttiUhler2018

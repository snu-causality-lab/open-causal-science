# Raskutti and Uhler (2018), sparsest permutations

<!-- topic: Discovery -->

Garvesh Raskutti and Caroline Uhler, *Learning directed acyclic graph models based on sparsest permutations*, Stat **7**(1), e183. The statement numbers and figure below refer to the authors' manuscript, arXiv:1307.0366v3. [Version of record](https://doi.org/10.1002/sta4.183) · [Authors' manuscript](https://hdl.handle.net/1721.1/130118)

## The DAG induced by an order

`orderDAG` selects a forward arrow when its endpoints are dependent given the other predecessors of its head. For an order with distinct ranks that respects a DAG, `graphOracle_predecessors_eq_not_edge` shows that this conditioning set separates the two vertices exactly when their arrow is absent. The proof uses ancestral moralization. Within the ancestral graph, all vertices except the two query endpoints are conditioned on, and the later endpoint has no child in that graph. Thus `orderDAG_recovers_graphOracle` reconstructs the given edge set from its graphical separation oracle. [Shared Lean definitions and proofs](../../OpenCausalScience/Discovery/OrderDAG.lean)

`orderDAG_subgraph_of_markov` proves the containment used in Lemma 2.2(a). For any Markov graph respecting the order, every arrow selected by the oracle must belong to that graph. If the induced DAG is Markov, this containment also proves the edge-deletion minimality conclusion of Lemma 2.1. With Markovness and adjacency faithfulness, a topological order recovers the original DAG. [Lean containment proof](../../OpenCausalScience/Papers/RaskuttiUhler2018/Minimality.lean)

The general graphoid result in Lemma 2.1 follows from the unique Markov boundary among the predecessors. Intersection turns the singleton tests into the ordered local Markov property. Ancestral moralization and the semigraphoid rules then yield the global property for disjoint sets. The resulting DAG is Markov and no proper subgraph is Markov. Strictly positive finite laws supply the required graphoid axioms. [Boundary](../../OpenCausalScience/Discovery/OrderBoundary.lean) · [Global Markov property](../../OpenCausalScience/Discovery/OrderedMarkov.lean) · [Finite laws](../../OpenCausalScience/Probability/FiniteGraphoid.lean)

## Exhaustive order search

The reference search enumerates all `n!` orders, returns every order attaining the minimum number of arrows and returns at least one order. Every Markov DAG has a topological order whose induced DAG is a subgraph. Therefore an order attaining the minimum also minimizes the number of arrows over all Markov DAGs. Under the graphoid premise and Markovness of the target DAG, the oracle search returns only DAGs equivalent to the target if and only if the sparsest Markov representation assumption holds, as in Theorem 2.4. [Enumeration](../../OpenCausalScience/Papers/RaskuttiUhler2018/SparsestPermutation.lean) · [Sparsest Markov representation](../../OpenCausalScience/Papers/RaskuttiUhler2018/SparsestRepresentation.lean)

## Figure 1

The orders `(1,2,3,4)` and `(1,4,3,2)` produce the drawn DAGs with distinct skeletons. A strictly positive binary law with denominator 256 realizes exactly the displayed singleton oracle, including the extra marginal independence between variables 1 and 4. Lean checks all 24 orders, with minimum four arrows, and connects the oracle to conditional independence of the normalized finite law. Thus both displayed DAGs are globally Markov for a concrete law and attain the minimum. [DAG replay](../../OpenCausalScience/Papers/RaskuttiUhler2018/Figure1.lean) · [Exact enumeration](../../OpenCausalScience/Papers/RaskuttiUhler2018/Figure1Distribution.lean) · [Probability law](../../OpenCausalScience/Papers/RaskuttiUhler2018/Figure1Law.lean)

## Statistical inference

A finite-query lemma proves that an oracle estimator inherits consistency when the error probability of each fixed query tends to zero. This supplies the reduction from sample CI decisions to the oracle theorem. The convergence of a particular CI test's error is a premise. The paper's high-dimensional rates also require additional uniform bounds for its statistical tests. [Finite-query reduction](../../OpenCausalScience/Discovery/OracleConsistency.lean)

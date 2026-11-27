# Raskutti and Uhler (2018), sparsest permutations

<!-- topic: Discovery -->

Garvesh Raskutti and Caroline Uhler, *Learning directed acyclic graph models based on sparsest permutations*, Stat **7**(1), e183. The statement numbers and figure below refer to the authors' manuscript, arXiv:1307.0366v3. [Version of record](https://doi.org/10.1002/sta4.183) · [Authors' manuscript](https://hdl.handle.net/1721.1/130118)

## The DAG induced by an order

`orderDAG` selects a forward arrow when its endpoints are dependent given the other predecessors of its head. For an order with distinct ranks that respects a DAG, `graphOracle_predecessors_eq_not_edge` shows that this conditioning set separates the two vertices exactly when their arrow is absent. The proof uses ancestral moralization. Within the ancestral graph, all vertices except the two query endpoints are conditioned on, and the later endpoint has no child in that graph. Thus `orderDAG_recovers_graphOracle` reconstructs the given edge set from its graphical separation oracle. [Shared Lean definitions and proofs](../../OpenCausalScience/Discovery/OrderDAG.lean)

`orderDAG_subgraph_of_markov` proves the containment used in Lemma 2.2(a). For any Markov graph respecting the order, every arrow selected by the oracle must belong to that graph. It also gives the edge-deletion minimality implication in Lemma 2.1. With Markovness and adjacency faithfulness, a topological order recovers the original DAG. The general Markovness of the induced graph under a graphoid distribution and the search over all permutations remain open in Lean. [Lean proofs](../../OpenCausalScience/Papers/RaskuttiUhler2018/Minimality.lean)

## Figure 1

The executable replay uses the graphical separations of Figure 1(a) and the stipulated additional marginal independence between variables 1 and 4. The orders `(1,2,3,4)` and `(1,4,3,2)` produce the two drawn four-edge DAGs. Their skeletons differ. This checks the two order projections using the stated CI oracle. Realizability of the oracle by a probability law and optimality over all orders are separate questions. [Lean replay](../../OpenCausalScience/Papers/RaskuttiUhler2018/Figure1.lean)

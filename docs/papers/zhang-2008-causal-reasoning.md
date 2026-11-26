# Zhang (2008), Causal Reasoning with Ancestral Graphs

<!-- topic: Graph equivalence -->

Jiji Zhang, *Causal Reasoning with Ancestral Graphs*, JMLR 9 (2008), 1437–1474. The check uses Definition 8, Lemma 9, Figure 6, and the proof in Appendix B of the journal version. [Journal article and PDF](https://www.jmlr.org/papers/v9/zhang08a.html)

## Visibility and inducing walks

An edge `A → B` in a MAG is visible when a vertex `C` nonadjacent to `B` has an edge into `A`, or has a collider path into `A` whose interior vertices are parents of `B`. In Lemma 9, an inducing path into `A` in the underlying DAG rules out such a witness when `A` is an ancestor of `B`.

Lean checks the concatenation argument for a finite mixed graph with an explicit no-selection projection interface. A projected arrow must preserve directed ancestry, and projected edge marks supply inducing witnesses that preserve arrowheads. The interface also requires that an inducing walk between distinct observed vertices implies adjacency in the projection. The proof combines the inducing pieces of the visibility witness with an inducing walk into `A`, making the witness vertex `C` adjacent to `B`.

| Statement | Lean declaration |
| --- | --- |
| A visible edge excludes an inducing walk into its source under the stated projection facts. | `visible_edge_excludes_inducing_walk_into_source` |
| Taking the bidirected edge as the inducing walk excludes a bidirected edge over the visible arrow in the underlying graph. | `visible_edge_excludes_bidirected_edge` |

The walk formulation allows repeated vertices and includes every path-shaped visibility witness in Figure 6. The projection interface is a mathematical premise of both declarations. [Lean source](../../OpenCausalScience/Papers/Zhang2008CausalReasoning/Visibility.lean)

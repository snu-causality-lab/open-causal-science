# Chickering (2002), Insert and Delete

<!-- topic: Discovery -->

[Paper index](../paper-checks.md)

> **Author correction** · [Appendix C, potential sinks](#potential-sink-condition) · The erratum replaces the clique test on neighbors and parents with adjacency requirements for the undirected neighbors.

Chickering's GES operators describe moves between Markov equivalence classes of DAGs using completed partially directed acyclic graphs. The companion formalizes the relationship between an operator's edge and collider changes and a single edit of a DAG extension. [JMLR article, Definitions 12–14, Theorems 15 and 17, and Appendix B](https://jmlr.org/papers/v3/chickering02b.html)

- [Insert.lean](../../OpenCausalScience/Papers/Chickering2002/Insert.lean) proves the matching-tails characterization from Lemma 41 for a single acyclic insertion. It proves the necessity of the clique condition in Theorem 15. Here the selected tails are the reversible parents of `Y` that are nonadjacent to `X`. When the extension chooses the required parents, blocking all semidirected walks from `Y` to `X` by `N(Y,X) ∪ T` suffices for acyclicity. The edited DAG matches the operator PDAG's skeleton and unshielded colliders and agrees with its prescribed arrows.
- [Delete.lean](../../OpenCausalScience/Papers/Chickering2002/Delete.lean) proves that a successful single-arrow deletion identifies the selected heads from new unshielded colliders, as in Lemma 42. It proves the necessity of the clique condition in Theorem 17 for a realization by a single DAG edit. The reverse direction takes as a premise that when a common child of `X,Y` is compelled to be a child of `Y`, it is also compelled to be a child of `X`. The original argument derives this premise from Proposition 33 and Lemma 34.

[DirectedEdgeEdit.lean](../../OpenCausalScience/Graph/DirectedEdgeEdit.lean) proves that adding `X → Y` to a DAG on distinct vertices admits an acyclic ranking exactly when the original graph has no directed path from `Y` to `X`. Deletion keeps the original topological ranking.

<a name="the-validity-tests-together"></a>

## The validity tests on essential graphs

[CPDAGOperators.lean](../../OpenCausalScience/Papers/Chickering2002/CPDAGOperators.lean) proves both directions of the Insert and Delete validity tests for admissible inputs on the essential graph of any finite DAG. [OperatorTests.lean](../../OpenCausalScience/Papers/Chickering2002/OperatorTests.lean) uses ordered chain components, inherited parents, and the ability to put a prescribed clique first. The essential-graph proof supplies all three properties from the DAG. In the tests below, `N(Y,X)` consists of reversible neighbors of `Y` adjacent to `X`. [Essential-graph structure](andersson-madigan-perlman-1997-essential-graphs.md)

- For Insert, the source tests are that `N(Y,X) ∪ T` is a clique and blocks all semidirected paths from `Y` to `X`. [InsertBlocking.lean](../../OpenCausalScience/Papers/Chickering2002/InsertBlocking.lean) proves that a shortest semidirected route avoiding that set is simple and has unshielded consecutive triples. In a representative satisfying the required parent configuration, the first arrow points out of `Y`. Reversing a later edge would create an unshielded collider, so the route would be directed from `Y` to `X` and close a cycle upon insertion.
- For Delete, the source test is that `N(Y,X) ∖ H` is a clique. The within-component vertex order gives a representative with `X → Y` and exactly `N(Y,X) ∖ H` as the reversible parents of `Y` apart from `X` itself. The arrow `X → Y` puts the component of `X` no later than that of `Y`. A common child reached by a fixed arrow from `Y` is therefore strictly later than `X` in the component order. The arrow from `X` is then fixed as well, supplying the triangle implication needed by Lemma 42. [CliqueExtensions.lean](../../OpenCausalScience/Papers/Chickering2002/CliqueExtensions.lean)

The result covers the graphical validity of the two operators. The two-phase large-sample theorem also requires the paper's score and distribution assumptions.

## Potential-sink condition

The published erratum corrects the potential-sink condition in Appendix C. Each undirected neighbor must be adjacent to the other undirected neighbors and to every parent. This is the condition used in the [PDAG extension companion](wienobst-bannach-liskiewicz-2021-pdag-extension.md). [Chickering's erratum](https://www.jmlr.org/papers/volume3/chickering02b/erratum.pdf)

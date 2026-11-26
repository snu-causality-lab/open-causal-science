# Chickering (2002), Insert and Delete

<!-- topic: Discovery -->

Chickering's GES operators describe moves between Markov equivalence classes of DAGs using completed partially directed acyclic graphs. The companion formalizes the relationship between an operator's edge and collider changes and a single edit of a DAG extension. [JMLR article, Definitions 12–14, Theorems 15 and 17, and Appendix B](https://jmlr.org/papers/v3/chickering02b.html)

- [Insert.lean](../../OpenCausalScience/Papers/Chickering2002/Insert.lean) proves the matching-tails characterization from Lemma 41 for a single acyclic insertion. It proves the necessity of the clique condition in Theorem 15. Here the selected tails are the reversible parents of `Y` that are nonadjacent to `X`. When the extension chooses the required parents, blocking all semidirected walks from `Y` to `X` by `N(Y,X) ∪ T` suffices for acyclicity. The edited DAG matches the operator PDAG's skeleton and unshielded colliders and agrees with its prescribed arrows.
- [Delete.lean](../../OpenCausalScience/Papers/Chickering2002/Delete.lean) proves that a successful single-arrow deletion identifies the selected heads from new unshielded colliders, as in Lemma 42. It proves the necessity of the clique condition in Theorem 17 for a realization by a single DAG edit. The reverse direction takes as a premise that when a common child of `X,Y` is compelled to be a child of `Y`, it is also compelled to be a child of `X`. The original argument derives this premise from Proposition 33 and Lemma 34.

[DirectedEdgeEdit.lean](../../OpenCausalScience/Graph/DirectedEdgeEdit.lean) proves that adding `X → Y` to a DAG on distinct vertices admits an acyclic ranking exactly when the original graph has no directed path from `Y` to `X`. Deletion keeps the original topological ranking.

The remaining operator proofs include constructing the parent-selection extension from the clique in Lemma 36 and deriving the necessary path-blocking test and the compelled-child triangle premise from the completed PDAG. The large-sample consistency of GES has separate assumptions about the score.

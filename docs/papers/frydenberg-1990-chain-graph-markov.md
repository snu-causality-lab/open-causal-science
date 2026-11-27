# Frydenberg (1990), the chain graph Markov property

<!-- topic: Graphical Markov models -->

Morten Frydenberg, *The Chain Graph Markov Property*, Scandinavian Journal of Statistics 17(4), 333–353. The LWF separation test restricts the graph to the ancestral components of the query, marries parents of each component, drops directions and separates in the resulting undirected graph. Theorem 5.6 characterizes LWF equivalence using the skeleton and minimal complexes. [Published article](https://www.jstor.org/stable/4616181)

- [MoralSeparation.lean](../../OpenCausalScience/Papers/Frydenberg1990/MoralSeparation.lean) defines the reference test. `separated_eq_true_iff` relates its Boolean result to reachability in the ancestral moral graph after conditioning vertices are removed. For distinct nonadjacent vertices, `nonadjacent_rank_separator` constructs a separating set by conditioning on the other vertices no higher than the largest endpoint rank. Direct adjacency survives every conditioning set disjoint from the endpoints. These facts give `equal_separations_same_skeleton` for finite chain graphs.
- [MinimalComplex.lean](../../OpenCausalScience/Papers/Frydenberg1990/MinimalComplex.lean) represents an induced path of the form `a → c₁ — ⋯ — cₖ ← b`. `ofDAG_lines_eq_zero` and `ofDAG_zero_complex_iff` identify its DAG specialization with the unshielded collider used in the [Verma–Pearl characterization](verma-pearl-1990-dag-equivalence.md).

The source uses disjoint query sets with nonempty endpoints. The proof of skeleton recovery uses queries of that kind. The general necessity of equal minimal complexes, sufficiency of the skeleton-and-complex criterion, and the equivalence between global and block-recursive probability statements remain open in Lean.

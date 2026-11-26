# Spirtes and Glymour (1991), oracle PC

<!-- topic: Discovery -->

PC starts with a complete skeleton, removes edges as separating sets are found, and orients an unshielded triple as a collider if its middle is absent from the saved separator. The Lean search uses the union of endpoint neighborhoods, as in the reported implementation. It uses the stored separators that the appendix credits to Pearl and Verma. It freezes the graph within each cardinality round, as in the later PC-stable schedule, and searches all cardinalities through the number of vertices. [Spirtes and Glymour, pp. 67–71](https://www.cse.sc.edu/~mgv/csce582sp14/presentations/SpirtesGlymourPC.pdf) · [Colombo and Maathuis (2014), Algorithm 4.1](https://www.jmlr.org/papers/volume15/colombo14a/colombo14a.pdf#page=13)

[OracleSkeleton.lean](../../OpenCausalScience/Papers/SpirtesGlymour1991/OracleSkeleton.lean) proves `skeleton_iff` and `collider_test_iff` for arbitrary finite DAGs given an exact independence oracle. `live_of_adjacent` shows that a true edge survives every round. For a missing edge, the parent set of one endpoint remains among the candidates and separates the pair. `bayes_ball_oracle_exact` supplies an executable oracle from the existing Bayes-ball proof.

The graph-level theorem uses exact agreement with d-separation for distinct endpoints outside the conditioning set. The sample CI tests, optional undirected-path pruning, running-time analysis, and directions beyond unshielded colliders have separate proof obligations. [Verma–Pearl companion](verma-pearl-1990-dag-equivalence.md) · [Meek orientation companion](meek-1995-orientation.md)

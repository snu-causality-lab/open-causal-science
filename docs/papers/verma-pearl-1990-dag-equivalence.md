# Verma and Pearl (1990), DAG equivalence

<!-- topic: Graph equivalence -->
<!-- index-anchor: verma-and-pearl-1990-dag-equivalence -->

[Paper index](../paper-checks.md)

[Lemmas 1–2 and Theorem 1](https://arxiv.org/pdf/1304.1108) characterize labelled DAG equivalence using the skeleton and unshielded colliders. [DAGEquivalence.lean](../../OpenCausalScience/Papers/VermaPearl1990/DAGEquivalence.lean) proves the necessary direction for equality of finite DAG d-separation answers. An arrow admits no separating query for its endpoints. Two nonadjacent vertices have a separating set drawn from the parents of one endpoint. In an unshielded triple, a separating set omits the middle if the triple is a collider and includes it otherwise. The executable signature test reflects the two graph conditions. A signature mismatch yields a query on which `DAG.dSeparated` gives different answers. Lean verifies equivalence of the three orientations in the five-vertex Figure 2 by comparing every legal query and distinguishes a fourth orientation. CPDAG construction and consistent extension remain separate results. [Executable queries](../../OpenCausalScience/Papers/VermaPearl1990/ExecutableQuery.lean) · [Figure 2](../../OpenCausalScience/Papers/VermaPearl1990/Figure2.lean)

## The sufficient direction

[Equivalence.lean](../../OpenCausalScience/Papers/VermaPearl1990/Equivalence.lean) proves `same_dConnections_iff_same_signature` for arbitrary finite DAGs with the same labelled vertex universe. From equality of skeletons and unshielded colliders, the [covered-reversal construction](chickering-1995-covered-reversals.md) reaches the target edge function. Each reversal preserves the query answers, and equal edge functions give the same answers for any choice of topological ranks. The theorem `signaturesMatch_iff_same_dConnections` relates the executable signature test to this equivalence.

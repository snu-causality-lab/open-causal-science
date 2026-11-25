# Verma and Pearl (1990), DAG equivalence

<!-- topic: Graph equivalence -->
<!-- index-anchor: verma-and-pearl-1990-dag-equivalence -->

[Paper index](../paper-checks.md)

[Lemmas 1–2 and Theorem 1](https://arxiv.org/pdf/1304.1108) characterize labelled DAG equivalence using the skeleton and unshielded colliders. [DAGEquivalence.lean](../../OpenCausalScience/Papers/VermaPearl1990/DAGEquivalence.lean) proves the necessary direction for equality of finite DAG d-separation answers. An arrow admits no separating query for its endpoints. Two nonadjacent vertices have a separating set drawn from the parents of one endpoint. In an unshielded triple, a separating set omits the middle if the triple is a collider and includes it otherwise. The executable signature test reflects the two graph conditions. A signature mismatch yields a query on which `DAG.dSeparated` gives different answers. Lean verifies equivalence of the three orientations in the five-vertex Figure 2 by comparing every legal query and distinguishes a fourth orientation. General sufficiency, CPDAG construction and consistent extension are separate results. [Executable queries](../../OpenCausalScience/Papers/VermaPearl1990/ExecutableQuery.lean) · [Figure 2](../../OpenCausalScience/Papers/VermaPearl1990/Figure2.lean)

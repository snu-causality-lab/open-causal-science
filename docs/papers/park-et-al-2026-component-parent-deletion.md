# Park et al. (2026), Breaking Bad

<!-- topic: Graph learning -->

[Paper index](../paper-checks.md)

*Breaking Bad: Component-Wise Parent Deletion for Score-Based Causal Discovery*,
UAI 2026, PMLR 337, pp. 5289–5331. The proceedings PDF has SHA-256
`613dfceb96057edfa1c6bb0347f358655727c01367ea54efd887d5815ddb4f30`.
[Proceedings](https://proceedings.mlr.press/v337/park26b.html)

## Theorem 2 — component-wise parent deletion

`component_parent_deletion_valid` proves that deleting all arrows entering
one chain component from outside leaves a partially directed graph admitting a
consistent DAG extension. The CPDAG is the semantic essential graph of a finite
DAG. Its arrows are the compelled edges, and its chain components and external
parent relationships come from the Andersson–Madigan–Perlman characterization.
The witness deletes precisely the same arrows in a representative DAG.
[Lean proof](../../OpenCausalScience/Papers/ParkEtAl2026/ComponentParentDeletion.lean)

When removing an external parent adjacency exposes a collider, one incoming
arrow crosses component boundaries. If the other incoming arrow were inside
the collider's component, parent inheritance would give an arrow opposite to
the deleted edge in the original DAG. Thus both incoming arrows of the new
unshielded collider are retained compelled edges. The proof covers graph
validity in Theorem 2. Score formulas, search dynamics and empirical results
have separate scopes.

# Richardson et al. (2023), nested Markov properties

<!-- topic: Identification -->

[Paper index](../paper-checks.md)

## Graphical fixing

Definition 19 changes a random vertex to fixed and removes every edge
with an arrowhead at that vertex. Lemma 22 shows that each other
currently fixable vertex remains fixable. [Annals of Statistics 51(1), §2.11](https://doi.org/10.1214/22-AOS2253)

[Fixing.lean](../../OpenCausalScience/Papers/RichardsonEtAl2023/Fixing.lean)
represents the random set by a list. Its directed and bidirected walks
for the fixability test lie inside the current random set. In a CADMG
this suffices because a directed path cannot enter a fixed vertex and
a bidirected edge cannot meet one.

- `fixable_after_fixing` proves Lemma 22 by lifting any remaining
  descendant and district witnesses to the original graph. The
  monotonicity proof also works for the deletion of any other vertex.
- `fixings_remove_arrowheads_at_fixed_set` proves that repeated fixing
  deletes exactly the arrowheads at vertices in the chosen set.
- `same_graph_after_fixing_same_set` checks the graph part of
  Theorem 31. Two sequences with the same fixed set leave the same
  edges. `fixings_retain_random_complement` gives the final random
  set as the complement within the initial random set.
- `reachable_after_fixable_choice` proves that when a target has a valid
  fixing order, any currently fixable vertex outside that target can
  be chosen first and the rest of the target remains reachable.

The probability-kernel part of Theorem 31 and the nested factorization
characterizations require additional results. [Version of record, §3.1](https://doi.org/10.1214/22-AOS2253)

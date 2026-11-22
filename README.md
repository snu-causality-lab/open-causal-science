# Open Causal Science

Open Causal Science connects classical results on causal graphs to runnable examples and Lean proofs. It follows [topics from a causal-inference course](docs/foundations.md), starting with d-separation in a finite DAG.

## Conditioning on a collider or its descendant

The first [Lean example](OpenCausalScience/DSeparation.lean) uses the graph `X → M ← Y`, `M → D`.

| Conditioning set | Relation between `X` and `Y` |
| --- | --- |
| `∅` | d-separated |
| `{M}` | d-connected |
| `{D}` | d-connected |

The example uses [Causalean's d-separation decision procedure and active-walk theorem](https://causalsmith.org/library/Graph/DSep/). It checks the outcomes by kernel reduction and proves that for any conditioning set excluding `X` and `Y` in this graph, d-separation is equivalent to the absence of an active walk between them. [Geiger, Verma and Pearl (1990)](https://doi.org/10.1002/net.3230200504) and [Shachter (1998)](https://web.stanford.edu/~shachter/pubs/bayesbl.pdf) are the sources for d-separation and Bayes Ball.

## Markov equivalence on the same skeleton

The [second example](OpenCausalScience/MarkovEquivalence.lean) changes the orientations on the same four vertices. The chain `X → M → Y` and fork `X ← M → Y`, both with `M → D`, satisfy the two conditions of the Verma–Pearl theorem: matching skeletons and unshielded colliders. The collider graph has that skeleton too. The empty conditioning set d-separates `X` and `Y` in the collider graph and d-connects them in the chain, so these two graphs belong to different equivalence classes. [Causalean's Markov equivalence theorem](https://causalsmith.org/library/Graph/MarkovEquiv/)

## Run the checks

Install [Elan](https://github.com/leanprover/elan) and run these commands from the project root. Elan reads `lean-toolchain`; the Lake manifest fixes the dependency revisions.

```sh
lake exe cache get Mathlib.Data.Finset.Max Mathlib.Data.Finset.Powerset Mathlib.Data.Fintype.EquivFin Mathlib.Data.Fintype.Prod Mathlib.Logic.Relation
lake build
lake env lean OpenCausalScience/Axioms.lean
```

The last command prints the transitive axiom dependencies of each result. The expected report uses at most the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.

The package uses Lean `v4.33.0` to match the [pinned Causalean revision](https://github.com/Jiyuan-Tan/CausalSmith/tree/a7085d88d2e4b30003db7097ca374f4718da0f01), which also fixes the Mathlib revision used by the example.

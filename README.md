# Open Causal Science

Open Causal Science connects classical results on causal graphs to runnable examples and Lean proofs. The [finite DAG library](OpenCausalScience/Graph.lean) uses Lean's bundled standard library. The first [course topics](docs/foundations.md) use this library to check d-separation and compare small graphs.

## Conditioning on a collider or its descendant

The first [Lean example](OpenCausalScience/Examples.lean) uses the graph `X → M ← Y`, `M → D`.

| Conditioning set | Relation between `X` and `Y` |
| --- | --- |
| `∅` | d-separated |
| `{M}` | d-connected |
| `{D}` | d-connected |

The [reference checker](OpenCausalScience/Separation.lean) searches simple paths and tests whether each interior vertex is active given the conditioning set. It returns `none` for coincident endpoints or conditioning on an endpoint. The graph library also proves that ranks strictly increase along every nonempty directed walk, ruling out directed cycles. [Geiger, Verma and Pearl (1990)](https://doi.org/10.1002/net.3230200504)

## Comparing d-separations on the same skeleton

The chain `X → M → Y` and fork `X ← M → Y`, both with `M → D`, agree on all 48 queries for ordered pairs of distinct endpoints and every conditioning subset of the remaining vertices. The collider graph shares the chain's skeleton. The empty conditioning set separates `X` and `Y` in the collider graph and connects them in the chain. Lean checks these statements for the three concrete graphs by computation.

## Run the checks

Install [Elan](https://github.com/leanprover/elan) and run these commands from the project root. Elan reads `lean-toolchain` and selects Lean `v4.36.0`.

```sh
lake build
lake env lean OpenCausalScience/Axioms.lean
```

The last command prints the transitive axiom dependencies of each result. The expected report uses at most the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.

The earlier comparison using Causalean's general Bayes Ball and Verma–Pearl proofs is available at Git tag `causalean-reference`. Use that revision's README and Lean `v4.33.0` to reproduce it. [Causalean's graph library](https://causalsmith.org/library/Graph/)

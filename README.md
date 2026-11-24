# Open Causal Science

Open Causal Science formalizes results from published research on causal graphs. The [paper checks](docs/paper-checks.md) identify the original statement and what Lean proves. The [homepage corrections](docs/errata.md) track the versions and statements under verification. The [finite DAG library](OpenCausalScience/Graph/DAG.lean) uses Lean's bundled standard library and provides the graph operations for these checks.

The first checks cover Witte et al.'s Figures 2B and 2F, the parent-pair loop discussed in van der Zander et al.'s corrigendum, and directed path blocking in front-door searches. The [foundations guide](docs/foundations.md) traces mathematical dependencies across related papers.

Import `OpenCausalScience.Core` to use the shared definitions and theorems or import an individual `OpenCausalScience.Papers` module to work with a published result. The [structure guide](docs/structure.md) explains module placement and naming.

## Conditioning on a collider or its descendant

The [Lean example](OpenCausalScience/Examples/DSeparation.lean) uses the graph `X → M ← Y`, `M → D`.

| Conditioning set | Relation between `X` and `Y` |
| --- | --- |
| `∅` | d-separated |
| `{M}` | d-connected |
| `{D}` | d-connected |

The [reference checker](OpenCausalScience/Graph/DSeparation.lean) searches simple paths and tests whether each interior vertex is active given the conditioning set. It returns `none` for coincident endpoints or conditioning on an endpoint. The graph library also proves that ranks strictly increase along every nonempty directed walk, ruling out directed cycles. [Geiger, Verma and Pearl (1990)](https://doi.org/10.1002/net.3230200504)

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

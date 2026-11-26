# Open Causal Science

Open Causal Science formalizes published results in causal inference and discovery. The [paper checks](docs/paper-checks.md) identify each source and the Lean statement. The [corrections index](docs/errata.md) tracks the versions and statements under verification.

Import `OpenCausalScience.Core` for finite DAGs, d-separation and rational event mass. The [structure guide](docs/structure.md) lists the shared and paper-specific modules. The [foundations guide](docs/foundations.md) traces dependencies across papers, and the [CGA proof map](docs/cga.md) links implemented operations to theorems and executable comparisons.

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

The last command prints the transitive axiom dependencies of the listed theorems. The expected report uses at most the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.

The root package uses Lean's bundled standard library. The optional [`analysis/`](analysis/) package uses Mathlib for [Tian–Pearl causal factors](docs/papers/tian-pearl-2003-q-decomposition.md), the connected-support argument for causal representation learning, and the [Beyond Bounds results](docs/papers/kim-cho-lee-2026-beyond-bounds.md). Run the following from the project root.

```sh
cd analysis
lake exe cache get
lake build
lake env lean -DwarningAsError=true FocusedAxioms.lean
```

The [counterfactual structural bandits package](analysis/ctf-scb/README.md) has its own build and checks the ICLR 2026 proceedings and corresponding structural results in the authors’ public follow-up. [Paper record](docs/papers/park-lee-2026-ctf-scb.md)

The earlier comparison used Causalean's general Bayes Ball and Verma–Pearl proofs with Lean `v4.33.0`. [Causalean's graph library](https://causalsmith.org/library/Graph/)

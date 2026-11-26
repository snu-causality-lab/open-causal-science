# Causal Graph Algorithms and Lean

These records relate CGA operations to the published statements and Lean results they use. The operations below are tested through the CGA Python API. The Lean code checks specific mathematical statements in its own graph representations. Each operation below names its proof scope so that a finite replay, a general theorem, and a complexity claim can be read in context. The [paper checks](paper-checks.md) give the source editions and declarations.

| CGA operation | Published statement or example | What Lean checks |
| --- | --- | --- |
| `d_separated`, `d_separated_sets` | Ancestral moralization and the active-path criterion. | On finite DAGs, deleting the conditioning set from the ancestral moral graph separates the query sets exactly when no active simple path joins them. The query sets are disjoint from the conditioning set. Lean also proves the Boolean ancestral-moral traversal implements this criterion. CGA uses the same reduction with undirected reachability. [Theorem 35](papers/perkovic-et-al-2018-dag-adjustment.md#ancestral-moralization) · [Bayes-ball worklist](papers/shachter-1998-bayes-ball.md) |
| `m_separated`, `m_separated_sets` | The active edge-path criterion for ancestral graphs and ADMGs. | On finite mixed graphs with the stated endpoint restriction, the incoming-arrowhead search returns separation exactly when no vertex-simple active path joins the query sets. Distinct directed and bidirected edges stay distinct on a bow. [Worklist theorem and scope](papers/richardson-spirtes-2002-ancestral-graphs.md#arrival-state-search) |
| `find_m_separator`, `find_minimal_m_separator` | Van der Zander, Liśkiewicz and Textor (2019), 2023 corrigendum, and [van der Zander and Liśkiewicz, FindMinSep, Proposition 5.2](https://proceedings.mlr.press/v115/van-der-zander20a.html). | The parent-pair count for the augmentation loop analyzed by the authors. CGA uses its own augmentation and boundary search. [Corrected loop analysis](papers/van-der-zander-et-al-2019-ancestral-graphs.md) |
| `adjustment_set_is_valid`, `find_adjustment_set`, `find_minimal_adjustment_set` | Perković et al. (2018), Definitions 3 and 6. | On finite DAGs, first-arrow reachability computes the forbidden set and deletes exactly the proper back-door edges. For mixed graphs with supplied visibility, Lean also proves the proper back-door deletion rule and the active-path inclusion after deletion. [Mixed-graph deletion](papers/perkovic-et-al-2018-dag-adjustment.md) [DAG construction](papers/perkovic-et-al-2018-dag-adjustment.md) · [Figure 2B](papers/witte-et-al-2020-efficient-adjustment.md#figure-2b) · [Figure 2F](papers/witte-et-al-2020-efficient-adjustment.md#figure-2f) |
| `dag_markov_equivalent` | Verma–Pearl (1990), Lemmas 1–2 and Theorem 1. | Equal d-separation implies a matching skeleton and set of unshielded colliders. A signature mismatch yields a distinguishing query. [DAG equivalence](papers/verma-pearl-1990-dag-equivalence.md) |
| `mag_markov_equivalent` | Ali–Richardson–Spirtes (2009), Proposition 3.6 and Figures 4 and 6. | Equivalent maximal graphs agree on adjacencies and unshielded colliders. The finite figure checks include two graphs with the same order-zero signature and different m-separations, and equivalent graphs in which the displayed vertex sequence has different discriminating-path status. [MAG equivalence](papers/ali-richardson-spirtes-2009-mag-equivalence.md) |
| `dag_optimal_adjustment_set`, `dag_forbidden_projection` | Henckel et al. O-set construction and Witte et al. Proposition 10. | In a finite DAG with disjoint treatment and outcome sets and the stated descendant premise, the O-set equals the outcome's parent set in the forbidden projection, excluding treatments and outcomes. [Henckel](papers/henckel-et-al-2022-dag-o-set.md) · [Witte](papers/witte-et-al-2020-efficient-adjustment.md#the-o-set-in-the-forbidden-projection) |
| `runge_o_set` | Runge's revised O-set Definitions 3–4. | The finite ADMG construction uses the stated eligibility test, and reduces to the parent part with no bidirected edges. [Runge](papers/runge-2021-o-set.md) |
| `meek_closure` | Meek's orientations. | The R1 conclusion follows in a DAG extension preserving the specified unshielded colliders, and R2 follows from acyclicity. [Meek](papers/meek-1995-orientation.md) |
| `find_directed_edge_visibility_witness` | Zhang's visibility criterion. | The visibility witness excludes an inducing walk into the source given the projection interface in the paper companion. [Zhang](papers/zhang-2008-causal-reasoning.md) |
| `identify_causal_effect`, `identify_pag_causal_effect` | Exact-query hedge reasoning and marginal IDP. | Shpitser's Figure 1(c) has a supported finite counterpair for the strict subquery. The two graph cuts and denominator scopes of Jaber et al.'s Figure 3(a) are checked. [Shpitser](papers/shpitser-2023-id-failure.md) · [Jaber](papers/jaber-et-al-2022-marginal-idp.md) |

The [Kivva et al. Example 2 check](papers/kivva-et-al-2022-general-identifiability.md) gives a reference for a generalized-identification regression. Its two models have structural zeros, which distinguishes their comparison from the strict-positive g-identification domain.

The [CGA repository](https://github.com/snu-causality-lab/cga) provides the Python and C implementations. Its [released replay scripts](https://github.com/snu-causality-lab/cga/releases/tag/v0.2.0a1) compare the Python API with the Lean exports below. The two projects build independently.

## Compare the m-separation examples

After `lake build`, run the exporter to obtain Lean's verdicts for every legal ordered singleton query on the nine four-vertex graphs in Richardson–Spirtes Figure 9 and Ali–Richardson–Spirtes Figures 4 and 6.

```sh
lake env lean replay/MSeparation.lean > m-separation.json
```

From the CGA v0.2.0a1 checkout with CGA installed, run the [released comparison script](https://github.com/snu-causality-lab/cga/blob/v0.2.0a1/tests/compare_lean_mseparation.py) against this JSON. It evaluates the graphs in CGA's paper fixtures independently. All 432 queries matched in the first comparison. The sequence is ordered by source vertex, target vertex, and conditioning bit mask in the figure's vertex order.

```sh
python tests/compare_lean_mseparation.py /path/to/m-separation.json
```

## Compare the DAG separation queries

The [Boolean implementation](../OpenCausalScience/Graph/MoralizationExecutable.lean) computes the reflexive ancestral set, follows skeleton and co-parent edges, and blocks the conditioned vertices. `Query.dagMoralSeparated_eq_true_iff` proves that its result agrees with the active-path definition. The executable replay enumerates the 64 DAGs on four vertices in one fixed topological order and all pairwise disjoint queries with nonempty endpoint sets.

```sh
lake env lean replay/DSeparation.lean > d-separation.json
```

The [CGA comparison](https://github.com/snu-causality-lab/cga/blob/v0.2.0a1/tests/compare_lean_dseparation.py) calls `d_separated_sets` through the installed Python package. All 7,040 queries agreed. The theorem covers arbitrary finite DAGs in Lean. The replay compares the Python implementation on the four-vertex domain.

```sh
python tests/compare_lean_dseparation.py /path/to/d-separation.json
```

## Compare the mixed-graph arrival search

The exporter enumerates the 64 three-vertex ADMGs in one fixed topological
order, the 72 three-vertex ancestral graphs, and two four-vertex graphs.
The four-vertex inputs exercise a bow and collider descendants, and an
ancestral graph with an undirected edge. It evaluates every legal
pairwise disjoint set query with nonempty endpoints on each graph.

```sh
lake env lean replay/MixedSeparation.lean > mixed-separation.json
```

From the CGA checkout with the [v0.2.0a1 wheel](https://github.com/snu-causality-lab/cga/releases/tag/v0.2.0a1)
installed, run the [mixed-graph comparison script](https://github.com/snu-causality-lab/cga/blob/main/tests/compare_lean_mixed_separation.py).
It compares the Lean output with the public `m_separated_sets` API and with
an independent oracle that enumerates simple edge-marked paths.

```sh
python tests/compare_lean_mixed_separation.py /path/to/mixed-separation.json
```

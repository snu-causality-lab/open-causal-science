# Causal Graph Algorithms and Lean

These records relate CGA operations to the published statements and Lean results they use. The operations below are tested through the CGA Python API. The Lean code checks specific mathematical statements in its own graph representations. Each operation below names its proof scope so that a finite replay, a general theorem, and a complexity claim can be read in context. The [paper checks](paper-checks.md) give the source editions and declarations.

| CGA operation | Published statement or example | What Lean checks |
| --- | --- | --- |
| `d_separated` | Directed path separation and Bayes-ball. | Lean reflects the simple-path test and proves correctness of a Bayes-ball worklist on finite DAGs. CGA's DAG evaluator uses ancestral moralization and undirected reachability. [Graph and worklist](papers/shachter-1998-bayes-ball.md) |
| `m_separated` | Richardson–Spirtes (2002), §3.4 and Figure 9. | Exact enumeration for simple endpoint-marked graph paths, and equality of separation signatures for the two graphs in Figure 9. The reference allows one edge per pair and includes undirected edges. [Mixed graphs](papers/richardson-spirtes-2002-ancestral-graphs.md) |
| `find_m_separator`, `find_minimal_m_separator` | Van der Zander, Liśkiewicz and Textor (2019), 2023 corrigendum, and [van der Zander and Liśkiewicz, FindMinSep, Proposition 5.2](https://proceedings.mlr.press/v115/van-der-zander20a.html). | The parent-pair count for the augmentation loop analyzed by the authors. CGA uses its own augmentation and boundary search. [Corrected loop analysis](papers/van-der-zander-et-al-2019-ancestral-graphs.md) |
| `adjustment_set_is_valid`, `find_adjustment_set`, `find_minimal_adjustment_set` | Perković et al. (2018), Definitions 3 and 6. | On finite DAGs, first-arrow reachability computes the forbidden set and deletes exactly the proper back-door edges. The Witte et al. cases check specific adjustments or projections. [DAG construction](papers/perkovic-et-al-2018-dag-adjustment.md) · [Figure 2B](papers/witte-et-al-2020-efficient-adjustment.md#figure-2b) · [Figure 2F](papers/witte-et-al-2020-efficient-adjustment.md#figure-2f) |
| `dag_markov_equivalent` | Verma–Pearl (1990), Lemmas 1–2 and Theorem 1. | Equal d-separation implies a matching skeleton and set of unshielded colliders. A signature mismatch yields a distinguishing query. [DAG equivalence](papers/verma-pearl-1990-dag-equivalence.md) |
| `mag_markov_equivalent` | Ali–Richardson–Spirtes (2009), Proposition 3.6 and Figures 4 and 6. | Equivalent maximal graphs agree on adjacencies and unshielded colliders. The finite figure checks include two graphs with the same order-zero signature and different m-separations, and equivalent graphs in which the displayed vertex sequence has different discriminating-path status. [MAG equivalence](papers/ali-richardson-spirtes-2009-mag-equivalence.md) |

The [Kivva et al. Example 2 check](papers/kivva-et-al-2022-general-identifiability.md) gives a reference for a generalized-identification regression. Its two models have structural zeros, which distinguishes their comparison from the strict-positive g-identification domain.

The [CGA repository](https://github.com/snu-causality-lab/cga) provides the Python implementation. The [v0.1.0a1 release](https://github.com/snu-causality-lab/cga/releases/tag/v0.1.0a1) provides the matching API and fixtures. Its [replay instructions](https://github.com/snu-causality-lab/cga/blob/v0.1.0a1/README.md#lean-and-paper-replays) identify the Lean revision. The two projects build independently.

## Compare the m-separation examples

After `lake build`, run the exporter to obtain Lean's verdicts for every legal ordered singleton query on the nine four-vertex graphs in Richardson–Spirtes Figure 9 and Ali–Richardson–Spirtes Figures 4 and 6.

```sh
lake env lean replay/MSeparation.lean > m-separation.json
```

From the CGA v0.1.0a1 checkout with CGA installed, run the [released comparison script](https://github.com/snu-causality-lab/cga/blob/v0.1.0a1/tests/compare_lean_mseparation.py) against this JSON. It evaluates the graphs in CGA's paper fixtures independently. All 432 queries matched in the first comparison. The sequence is ordered by source vertex, target vertex, and conditioning bit mask in the figure's vertex order.

```sh
python tests/compare_lean_mseparation.py /path/to/m-separation.json
```

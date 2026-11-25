# Causal Graph Algorithms and Lean

These records relate CGA operations to the published statements and Lean results they use. CGA evaluates graph queries in its Python and native implementations. The Lean code checks specific mathematical statements in its own graph representations. Each operation below names its proof scope so that a finite replay, a general theorem, and a complexity claim can be read in context. The [paper checks](paper-checks.md) give the source editions and declarations.

| CGA operation | Published statement or example | What Lean checks |
| --- | --- | --- |
| `d_separated` | Directed path separation and Bayes-ball. | Active-path examples and agreement of a directional worklist with the simple-path criterion on finite DAGs. [Graph and worklist](paper-checks.md#finite-dag-and-ancestral-graph-separation) |
| `m_separated` | Richardson–Spirtes (2002), §3.4 and Figure 9. | Exact enumeration for simple endpoint-marked graph paths, and equality of separation signatures for the two graphs in Figure 9. The reference allows one edge per pair and includes undirected edges. [Mixed graphs](paper-checks.md#finite-dag-and-ancestral-graph-separation) |
| `find_m_separator`, `find_minimal_m_separator` | Van der Zander, Liśkiewicz and Textor (2019), 2023 corrigendum. | The parent-pair count for the augmentation loop analyzed by the authors. CGA uses its own augmentation and boundary search. [Corrected loop analysis](paper-checks.md#van-der-zander-liśkiewicz-and-textor-2019-2023-lemma-2) |
| `adjustment_set_is_valid`, `find_adjustment_set`, `find_minimal_adjustment_set` | Perković et al. (2018), Definitions 3 and 6. | On finite DAGs, first-arrow reachability computes the forbidden set and deletes exactly the proper back-door edges. The Witte et al. cases check specific adjustments or projections. [DAG construction](paper-checks.md#perković-et-al-2018-dag-adjustment) · [Figure 2B](paper-checks.md#witte-et-al-2020-figure-2b) · [Figure 2F](paper-checks.md#witte-et-al-2020-figure-2f) |
| `dag_markov_equivalent` | Verma–Pearl (1990), Lemmas 1–2 and Theorem 1. | Equal d-separation implies a matching skeleton and set of unshielded colliders. A signature mismatch yields a distinguishing query. [DAG equivalence](paper-checks.md#verma-and-pearl-1990-dag-equivalence) |
| `mag_markov_equivalent` | Ali–Richardson–Spirtes (2009), Proposition 3.6 and Figures 4 and 6. | Equivalent maximal graphs agree on adjacencies and unshielded colliders. The finite figure checks include two graphs with the same order-zero signature and different m-separations, and equivalent graphs in which the displayed vertex sequence has different discriminating-path status. [MAG equivalence](paper-checks.md#ali-richardson-and-spirtes-2009-mag-equivalence) |

The [Kivva et al. Example 2 check](paper-checks.md#kivva-et-al-2022-example-2) gives a reference for a generalized-identification regression. Its two models have structural zeros, which distinguishes their comparison from the strict-positive g-identification domain.

The CGA release is being prepared locally. Once published, each entry can link the released API and fixture revision. A CGA release can link a specific Lean revision for the statement it uses. Both builds use their own dependency lists.

## Compare the m-separation examples

After `lake build`, run the exporter to obtain Lean's verdicts for every legal ordered singleton query on the nine four-vertex graphs in Richardson–Spirtes Figure 9 and Ali–Richardson–Spirtes Figures 4 and 6.

```sh
lake env lean replay/MSeparation.lean > m-separation.json
```

The CGA candidate compares the output independently against the graphs in its own published-paper fixtures. All 432 queries matched in the first comparison. The sequence is ordered by source vertex, target vertex, and conditioning bit mask in the figure's vertex order.

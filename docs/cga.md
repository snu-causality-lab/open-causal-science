# Causal Graph Algorithms and Lean

These records relate CGA operations to the published statements and Lean results they use. The operations below are tested through the CGA Python API. The Lean code checks specific mathematical statements in its own graph representations. Each operation below names its proof scope so that a finite replay, a general theorem, and a complexity claim can be read in context. The [paper checks](paper-checks.md) give the source editions and declarations.

| CGA operation | Published statement or example | What Lean checks |
| --- | --- | --- |
| `d_separated`, `d_separated_sets` | Ancestral moralization and the active-path criterion. | On finite DAGs, deleting the conditioning set from the ancestral moral graph separates the query sets exactly when no active simple path joins them. The query sets are disjoint from the conditioning set. Lean also proves the Boolean ancestral-moral traversal implements this criterion. CGA uses the same reduction with undirected reachability. [Theorem 35](papers/perkovic-et-al-2018-dag-adjustment.md#ancestral-moralization) · [Bayes-ball worklist](papers/shachter-1998-bayes-ball.md) |
| `m_separated`, `m_separated_sets` | The active edge-path criterion for ancestral graphs and ADMGs. | On finite mixed graphs with the stated endpoint restriction, the incoming-arrowhead search returns separation exactly when no vertex-simple active path joins the query sets. Distinct directed and bidirected edges stay distinct on a bow. [Worklist theorem and scope](papers/richardson-spirtes-2002-ancestral-graphs.md#arrival-state-search) |
| `find_m_separator`, `find_minimal_m_separator` | Van der Zander, Liśkiewicz and Textor (2019), the 2023 corrigendum, and van der Zander and Liśkiewicz (2020). | The corrected parent-pair count and the correctness of the authors' two-pass algorithm on finite DAGs with required and allowed vertices. CGA uses its own augmentation and boundary search. [Corrected loop analysis](papers/van-der-zander-et-al-2019-ancestral-graphs.md) · [Finite DAG FindMinSep](papers/van-der-zander-liskiewicz-2020-minimal-separators.md) |
| `adjustment_set_is_valid`, `find_adjustment_set`, `find_minimal_adjustment_set` | Perković et al. (2018), Definitions 3 and 6. | On finite DAGs, first-arrow reachability computes the forbidden set and deletes exactly the proper back-door edges. For fully oriented graphs under the companion's amenability and forbidden-set assumptions, active proper noncausal paths exist exactly when the proper back-door graph has an active connection. [Mixed-graph blocking](papers/perkovic-et-al-2018-dag-adjustment.md) [DAG construction](papers/perkovic-et-al-2018-dag-adjustment.md) · [Figure 2B](papers/witte-et-al-2020-efficient-adjustment.md#figure-2b) · [Figure 2F](papers/witte-et-al-2020-efficient-adjustment.md#figure-2f) |
| `dag_markov_equivalent` | Verma–Pearl (1990), Lemmas 1–2 and Theorem 1. | The finite Lean signature test returns true exactly when every graphical d-separation query agrees. A mismatch yields a distinguishing query. [DAG equivalence](papers/verma-pearl-1990-dag-equivalence.md) |
| `CPDAG.from_dag`, `find_consistent_dag_extension` | Andersson–Madigan–Perlman Proposition 4.1 and the potential-sink criterion from Dor–Tarsi and Wienöbst et al. | The semantic essential graph has ordered chordal components, and a consistent DAG extension exists exactly when a potential-sink elimination order exists. Removing any potential sink preserves extendability. [Essential graphs](papers/andersson-madigan-perlman-1997-essential-graphs.md) · [PDAG extension](papers/wienobst-bannach-liskiewicz-2021-pdag-extension.md) |
| `mag_markov_equivalent` | Ali–Richardson–Spirtes (2009), Proposition 3.6 and Figures 4 and 6. | Equivalent maximal graphs agree on adjacencies and unshielded colliders. The finite figure checks include two graphs with the same order-zero signature and different m-separations, and equivalent graphs in which the displayed vertex sequence has different discriminating-path status. [MAG equivalence](papers/ali-richardson-spirtes-2009-mag-equivalence.md) |
| `dag_optimal_adjustment_set`, `dag_forbidden_projection` | Henckel et al. O-set construction and Witte et al. Proposition 10. | In a finite DAG with disjoint treatment and outcome sets and the stated descendant premise, the O-set equals the outcome's parent set in the forbidden projection, excluding treatments and outcomes. [Henckel](papers/henckel-et-al-2022-dag-o-set.md) · [Witte](papers/witte-et-al-2020-efficient-adjustment.md#the-o-set-in-the-forbidden-projection) |
| `runge_o_set` | Runge's revised O-set Definitions 3–4. | The finite ADMG construction uses the stated eligibility test, and reduces to the parent part with no bidirected edges. [Runge](papers/runge-2021-o-set.md) |
| `smucler_adjustment_set` | Smucler–Sapienza–Rotnitzky's efficiency graph. | Projecting away ignored vertices preserves separation with the required policy covariates conditioned on. Cuts correspond to eligible ancestral graphical adjustment sets with the stated restrictions. [Efficiency graph](papers/smucler-et-al-2022-adjustment-efficiency-graph.md) |
| `meek_closure` | Meek's orientations. | R1–R4 preserve the set of consistent extensions through all rounds. The closure is maximal on complete skeletons. [Meek](papers/meek-1995-orientation.md) |
| `find_directed_edge_visibility_witness` | Zhang's visibility criterion. | The visibility witness excludes an inducing walk into the source given the projection interface in the paper companion. [Zhang](papers/zhang-2008-causal-reasoning.md) |
| `identify_causal_effect`, `identify_pag_causal_effect` | Exact-query hedge reasoning and marginal IDP. | Shpitser's Figure 1(c) has a supported finite counterpair for the strict subquery. Its graphical obstruction persists through valid fixing orders. Jaber et al.'s Figure 3(a) graph cuts and the bucket quotient under explicit mechanism and support assumptions are checked. [Shpitser](papers/shpitser-2023-id-failure.md) · [Jaber](papers/jaber-et-al-2022-marginal-idp.md) |
| `identify_conditional_causal_effect`, `find_fixing_sequence` | IDC and graphical fixing. | The conditional identification proof composes one supported Rule 2 exchange with normalization of the reduced joint. On finite ADMGs, Tian's failure test agrees with the joint ID decision after exhausting exchanges. The graphical fixing proof preserves other fixable choices and shows final graph equality. [IDC](papers/shpitser-pearl-2006-conditional-idc.md) · [Failure agreement](papers/tian-2004-conditional-effects.md) · [Fixing](papers/richardson-et-al-2023-nested-markov.md) |
| `identify_mpdag_causal_effect` | Perković's partial causal ordering. | The bucket order and its projection to the query vertex set are correct given component labels, which are proved to exist. The paper example includes a directed edge within a bucket. [MPDAG partial causal order](papers/perkovic-2020-partial-causal-order.md) |
| `identify_counterfactual`, `identify_conditional_counterfactual` | Single-world reductions and source selection. | The Lean companions check shared-exogenous graph merging, the worked ID* and IDC* trace, finite unnesting, and source lookup for a supplied CTFIDU factor. CGA's value API handles its documented single-world routes and logical cases. [ID* and IDC*](papers/shpitser-pearl-2008-counterfactual-id.md) · [CTFIDU and CTFID](papers/correa-lee-bareinboim-2021-counterfactual-identification.md) · [CGA scope](https://github.com/snu-causality-lab/cga/blob/v0.2.0a1/docs/reference/PUBLISHED_IDENTIFICATION.md#counterfactuals) |
| `recover_conditional_distribution` | Conditional recovery from selected data. | The selected and population conditional cells coincide under the stated separation and support. Lean also checks the external-separator search and published positive and negative examples. [Bareinboim, Tian and Pearl 2014](papers/bareinboim-tian-pearl-2014-selection-recovery.md) |
| `recover_causal_effect` | Selected-only RC. | Lean verifies the recursive graph plan and its successful execution from the local kernel laws. The six-vertex public fixture gives an instance where RC stops and selected-only adjustment still recovers the effect. [RC](papers/bareinboim-tian-2015-selection-recovery.md) · [Counterexample](papers/correa-tian-bareinboim-2019-selection-identification.md#where-the-selected-only-rc-procedure-stops) |
| `selection_adjustment_pair_is_valid`, `find_selection_adjustment_pair`, `iter_selection_adjustment_pairs` | Generalized adjustment with selected data and an optional population margin. | The Boolean predicate implements Definition 9, including proper first arrows and source availability. Lean checks the two-source formula under explicit support and local probability identities. [Correa, Tian and Bareinboim 2018](papers/correa-tian-bareinboim-2018-selection-adjustment.md) |
| `recover_causal_effect_with_external_data` | IDSB and RCE with a same-population margin. | Lean checks population extension, the mixed-source district product under its local prefix identities, and the worked RCE graph trace. Figure 2(b)'s ratio recovers the response in a finite product-noise model. [Correa, Tian and Bareinboim 2019](papers/correa-tian-bareinboim-2019-selection-identification.md) |
| `hedge_hull`, `find_minimum_cost_intervention` | Akbari et al., single-district intervention design. | Lean proves the graph fixed point, hedge hitting equivalence and the paper example. CGA searches by recomputing the hull after a candidate intervention. [Akbari et al.](papers/akbari-et-al-2025-optimal-experiment-design.md) |
| `dag_intervention_markov_equivalent` | Hauser and Bühlmann, perfect-intervention cut graphs. | Lean proves equivalence of cut separation and cut signatures and the conservative-family criterion. Both projects reproduce the split in Figure 2. [Hauser and Bühlmann](papers/hauser-buhlmann-2012-interventional-equivalence.md) |
| `ida_parent_sets`, `joint_ida_parent_sets`, `joint_ida_parent_counts` | Maathuis et al.'s local IDA and Nandy et al.'s joint-IDA. | Lean verifies the local extension criterion and joint support by chain components. CGA also enumerates semi-local multiplicities. [IDA](papers/maathuis-kalisch-buhlmann-2009-ida.md) · [Joint-IDA](papers/nandy-maathuis-richardson-2017-joint-ida.md) |

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

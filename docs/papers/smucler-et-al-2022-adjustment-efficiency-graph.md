# Smucler, Sapienza and Rotnitzky (2022), adjustment efficiency graph

<!-- topic: Adjustment -->

[Paper index](../paper-checks.md)

Definition 6 forms the undirected graph H₁ by projecting out hidden or forbidden ancestral vertices of H₀ and joining each policy covariate to treatment and outcome. Lemma 3 identifies separation in H₀ and H₁ for retained endpoints and a conditioning set W with L ⊆ W ⊆ V(H₁). The proof follows Definition 6 and Lemma 3 in the pinned preprint. [arXiv:2004.10521v3, §§6 and 9.3](https://arxiv.org/pdf/2004.10521v3) · [Biometrika edition](https://doi.org/10.1093/biomet/asab018)

`EfficiencyGraph.h0_separation_iff_h1_separation` proves Lemma 3 on finite DAGs with single treatment and outcome vertices. H₀ is the moralization of the proper back-door graph restricted to the original DAG's ancestors of treatment, outcome and L. For the projection, each shortcut connects retained vertices by a walk whose interior vertices were removed. Expanding a shortcut preserves avoidance of W. Conversely, removing ignored vertices from a walk gives a walk in H₁. The extra policy edges cannot occur on an H₁ walk avoiding W because L ⊆ W. [EfficiencyGraph.lean](../../OpenCausalScience/Papers/SmuclerEtAl2022/EfficiencyGraph.lean)

`EfficiencyGraph.vertex_cut_iff_eligible_h0_separator` also checks that every H₁ treatment–outcome cut contains L. It assumes each policy covariate is retained and distinct from both endpoints. Under the same hypothesis, `EfficiencyGraph.vertex_cut_iff_ancestral_graphical_adjustment` proves the graphical correspondence used in Lemma 6(1–2). An H₁ cut is exactly a set containing L, made of observed ancestral covariates that exclude the endpoints and forbidden vertices, and d-separating treatment from outcome in the proper back-door graph. The proof establishes equality of the relevant ancestral scopes before applying the DAG moralization theorem. [EfficiencyGraph.lean](../../OpenCausalScience/Papers/SmuclerEtAl2022/EfficiencyGraph.lean)

The proof covers the graph construction and separation criterion. Equivalence with static or dynamic adjustment under the statistical model, efficiency and minimum-cardinality claims, and verification of the Python traversal remain separate. The public CGA implementation constructs H₁ by joining the retained boundary of each connected component of ignored vertices. [CGA, pinned implementation](https://github.com/snu-causality-lab/cga/blob/8a12610b3ac58d8f6c2f543759ebd2ee6d14ee2b/python/src/causal_graph_algorithms/smucler_adjustment.py)

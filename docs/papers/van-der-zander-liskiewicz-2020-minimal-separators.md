# Van der Zander and Liśkiewicz (2020), finding minimal d-separators

<!-- topic: Graph separation -->

[Paper index](../paper-checks.md)

Section 3 and Figure 3 describe `FindMinSepInDAG`. Given endpoint sets X and Y, required vertices I, and allowed vertices R, it starts with the allowed ancestors of X ∪ Y ∪ I. The two directional searches prune this set from opposite sides while retaining I. When a permitted separator exists, the algorithm returns a separator Z with I ⊆ Z ⊆ R and no proper subset still separating X and Y while containing I. [PMLR 115, pp. 637–647](https://proceedings.mlr.press/v115/van-der-zander20a.html) · [§3, Figure 3](https://proceedings.mlr.press/v115/van-der-zander20a/van-der-zander20a.pdf#page=4)

`FindMinSepInDAG.find_min_sep_in_dag_correct` proves this characterization for the finite DAG procedure with set-valued endpoints, I ⊆ R, and R disjoint from both endpoints. The proof also shows that `none` rules out every permitted separator, including candidates with non-ancestral vertices. `FindMinSepInDAG.dag_reach_iff_moral_reach` equates the directed arrival-state search with boundary reachability in the fixed ancestral moral graph. Each optional vertex of the output has a witness from both sides, so omitting it in any allowed subset of the output would connect the endpoints. [FindMinSepInDAG.lean](../../OpenCausalScience/Papers/VanDerZanderLiskiewicz2020/FindMinSepInDAG.lean)

`FindMinSepInDAG.find_min_sep_refines_spec` verifies the executable finite worklist, and `FindMinSepInDAG.find_min_sep_correct` gives its correctness directly. [FindMinSepInDAG.lean](../../OpenCausalScience/Papers/VanDerZanderLiskiewicz2020/FindMinSepInDAG.lean)

## Mixed-graph minimal separators

Proposition 5.2 gives the two-sided pruning construction for mixed graphs. CGA materializes the collider augmentation on the anterior set and searches its undirected boundary. Lean checks the anterior and collider worklists, proves the reduction to separation in that augmentation, and verifies both pruning passes. [§5, Proposition 5.2](https://proceedings.mlr.press/v115/van-der-zander20a/van-der-zander20a.pdf#page=7) · [CGA implementation](https://github.com/snu-causality-lab/cga/blob/61cc073a94cba296da1a539e0325eec16d5e355c/python/src/causal_graph_algorithms/separators.py)

`MixedGraph.find_minimal_m_separator_correct` covers finite marked graphs with symmetric, loop-free edges and no arrowhead incident to an undirected endpoint. For disjoint endpoints and covariates with I ⊆ R, its returned set Z is an inclusion-minimal m-separator among sets between I and R. If the function returns `none`, no set in that interval m-separates the endpoints. The proof establishes correctness of outputs. CGA uses the two boundary searches on a materialized graph, with costs specific to that construction. [MixedSeparators.lean](../../OpenCausalScience/Graph/MixedSeparators.lean) · [CGA replay](../cga.md#compare-constrained-minimal-m-separators)

`MixedGraph.find_minimal_admg_separator_correct` proves the same contract for the CGA route that adds one latent parent per bidirected edge and excludes these parents from the allowed set. The expansion preserves m-connection on the observed vertices, including when a directed and a bidirected edge share endpoints. [LatentExpansionSeparation.lean](../../OpenCausalScience/Graph/LatentExpansionSeparation.lean)

`MixedGraph.find_m_separator_correct` verifies the constrained existence search. `MixedGraph.m_separator_is_minimal_correct` verifies the minimality check for a supplied set, including rejection of sets with a vertex outside the anterior closure of the query endpoints and required vertices. [§5, Proposition 5.1](https://proceedings.mlr.press/v115/van-der-zander20a/van-der-zander20a.pdf#page=6) · [MixedSeparatorChecks.lean](../../OpenCausalScience/Graph/MixedSeparatorChecks.lean)

# Runge (2021), the O-set construction

<!-- topic: Adjustment -->

[Paper index](../paper-checks.md)

*Necessary and sufficient graphical conditions for optimal adjustment sets in causal graphical models with hidden variables* appeared at NeurIPS 2021. This companion follows Definitions 3 and 4 in the written supplement included in arXiv v4 (June 2023). [Proceedings](https://proceedings.neurips.cc/paper/2021/hash/8485ae387a981d783f8764e508151cd9-Abstract.html) · [arXiv:2102.10324v4](https://arxiv.org/html/2102.10324v4#S2.SS3)

[OSet.lean](../../OpenCausalScience/Papers/Runge2021/OSet.lean) defines the parents of the outcome and mediators outside the forbidden set, the valid bidirected collider chains, and the parents of their collider nodes for a finite ADMG with a singleton treatment and outcome. `Eligible` takes the separation test relative to the fixed valid ancestor set. `collider_eligible` proves that every vertex included from a chain satisfies both conditions of Definition 3. `o_set_iff_parent_part_without_bidirected` proves the reduction to the parent part when the graph has no bidirected edges. The supplied conditioning set is fixed throughout.

Causal Graph Algorithms (CGA) implements the construction for its documented input domain. The Lean declarations here check graph definitions and the reduction without bidirected edges. Theorem 1's general validity result and Theorem 3's information comparisons under Conditions I and II remain open in this Lean library. [CGA implementation and source discussion](https://github.com/snu-causality-lab/cga/blob/v0.2.0a1/docs/reference/RUNGE_ADJUSTMENT.md)

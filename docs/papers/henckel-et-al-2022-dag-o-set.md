# Henckel, Perković and Maathuis (2022), the O-set in a DAG

<!-- topic: Adjustment -->

[Paper index](../paper-checks.md)

The DAG case of Definition 3.12 of [arXiv:1907.02435v2](https://arxiv.org/abs/1907.02435v2) defines the O-set as the parents of causal nodes outside the forbidden set. A causal node is a non-treatment vertex on a proper directed treatment-to-outcome path. The forbidden set contains the treatments and the descendants of the causal nodes. The journal article appeared in *Journal of the Royal Statistical Society: Series B*, 84(2), 579–599. [Publication](https://doi.org/10.1111/rssb.12451)

[DAGOSet.lean](../../OpenCausalScience/Papers/HenckelEtAl2022/DAGOSet.lean) defines `CausalNode`, `Forbidden` and `OSet` on finite DAGs. `causal_node_iff` proves that a vertex outside the treatment set is a causal node exactly when a treatment reaches it by a directed walk and it has a treatment-free directed suffix to an outcome. The prefix can start again at the last treatment on the walk. The proof assumes disjoint treatments and outcomes when the definition is applied to the paper's query domain.

This construction is used to prove the [forbidden-projection representation of the O-set](witte-et-al-2020-efficient-adjustment.md#the-o-set-in-the-forbidden-projection). The Lean statements here concern graph membership. The pruning, maximal-PDAG and linear-model variance results require additional proofs.

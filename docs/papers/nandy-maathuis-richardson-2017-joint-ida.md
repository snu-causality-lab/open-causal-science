# Nandy, Maathuis and Richardson (2017), joint-IDA

<!-- topic: Graph equivalence -->

[Paper index](../paper-checks.md)

Algorithm 5.1 enumerates jointly valid parent tuples for several interventions from a true CPDAG. Theorem 5.1 compares the semi-local enumeration with the full enumeration. The same distinct tuples occur, and the ratios of their multiplicities agree. [Annals of Statistics, §5](https://doi.org/10.1214/16-AOS1462) · [Author copy, Theorem 5.1](https://arxiv.org/pdf/1407.2451#page=18)

[JointIDA.lean](../../OpenCausalScience/Papers/NandyEtAl2017/JointIDA.lean) proves the support part of Theorem 5.1. `joint_parent_support_iff_componentwise` characterizes the tuples realized by a global representative DAG. Targets in the same chain component must agree with one collider-free orientation of that component. The orientations of distinct components can be assembled independently, with compelled parents preserved. The construction orders all edges crossing components by the [essential-graph component order](andersson-madigan-perlman-1997-essential-graphs.md). It does not calculate causal effects or compare general multiplicities.

## Figure 2 and Example 3

The CPDAG is `1 — 3 — 2`. The candidate DAGs yield the tuples `(∅, {3})`, `({3}, ∅)`, and `({3}, {3})` at treatments `(1, 2)`. Lean checks the four orientations of the path using the [DAG equivalence signature](verma-pearl-1990-dag-equivalence.md). It also proves that each treatment separately can have no parents and that no equivalent DAG realizes both empty sets. Both empty sets would force `1 → 3 ← 2`, introducing an unshielded collider. The single-treatment projection onto vertex `1` records the multiplicity difference of [local IDA](maathuis-kalisch-buhlmann-2009-ida.md). [Author copy, Figure 2 and Example 3](https://arxiv.org/pdf/1407.2451#page=16)

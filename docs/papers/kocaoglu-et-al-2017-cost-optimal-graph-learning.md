# Kocaoglu, Dimakis and Vishwanath (2017), cost-optimal learning of causal graphs

<!-- topic: Experimental design -->

[Paper index](../paper-checks.md)

A fixed experimental design is chosen to distinguish every causal DAG
with a given skeleton. Each perfect randomized intervention has a
known target, and the cost of an experiment adds the costs of its
targeted vertices. [ICML proceedings](https://proceedings.mlr.press/v70/kocaoglu17a.html)

## Separating every skeleton edge

[SeparatingDesign.lean](../../OpenCausalScience/Papers/KocaogluEtAl2017/SeparatingDesign.lean)
formalizes Theorem 1 at the graph level.
`identifies_every_orientation_iff_separates_skeleton` says that a design
distinguishes all orientations of a fixed labelled skeleton exactly
when every skeleton edge has an experiment targeting exactly one of
its endpoints. A separating experiment exposes the direction in the
[cut skeleton](hauser-buhlmann-2012-interventional-equivalence.md).
For an unseparated edge, the proof puts its two endpoints first in a
topological order. The resulting covered edge can be reversed while
preserving observational d-connections and all the supplied cut
d-connections. `separatesCheck_iff` connects the Boolean test to the
formal design criterion.
[Theorem 1, p. 1878](https://proceedings.mlr.press/v70/kocaoglu17a/kocaoglu17a.pdf#page=4)

## Minimum additive cost with unrestricted experiment count

[MinimumCost.lean](../../OpenCausalScience/Papers/KocaogluEtAl2017/MinimumCost.lean)
checks the cost argument behind Theorem 2 for nonnegative rational
vertex weights. The union of the targets of a separating design is
a vertex cover. Counting each vertex in the union once costs at
most the design cost, which pays for every occurrence. Conversely,
one singleton experiment for each vertex in a cover separates every
edge and costs exactly the weight of the cover.
`minimum_cover_gives_optimal_design` proves that a minimum-weight
cover attains the optimal design cost.

This cost argument applies to any finite skeleton when the number of
experiments is unrestricted. The paper's chordal-graph algorithms,
color-class grouping, and bounded experiment-count results remain
outside the formalized results.
[Theorem 2, p. 1879](https://proceedings.mlr.press/v70/kocaoglu17a/kocaoglu17a.pdf#page=5)

## Figure 1

[Figure1.lean](../../OpenCausalScience/Papers/KocaogluEtAl2017/Figure1.lean)
checks that both displayed two-experiment designs separate every
skeleton edge. The left design assigns the same target membership
to `U₄` and `U₅`. Every proper three-coloring gives those vertices
distinct colors. This verifies the distinction in Proposition 1
between separating the skeleton edges and separating all distinct
color classes of a proper three-coloring.
[Proposition 1 and Figure 1](https://proceedings.mlr.press/v70/kocaoglu17a/kocaoglu17a.pdf#page=5)

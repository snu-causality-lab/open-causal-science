# Shpitser (2023), hedges for the exact query

<!-- topic: Identification -->

[Paper index](../paper-checks.md)

Figure 1(b–c) distinguishes the effect of setting both `A₁,A₂` on `Y`
from the effect of setting only `A₂`. The latter has a hedge. The
former has an identifying formula. Proposition 1 replaces the earlier
arbitrary-subquery hedge condition by a criterion for the query itself.
The drawing labels the summation variable `W`, which appears as `C`
in the printed formula. [arXiv:2307.03750v1, Figure 1 and Proposition 1](https://arxiv.org/pdf/2307.03750v1)

[Figure1C.lean](../../OpenCausalScience/Papers/Shpitser2023/Figure1C.lean)
uses the parent sets of Figure 1(b) to construct two binary SCMs.
The primitive roots are independent, and allowed arguments can be
inactive. `positive_observational_agreement` checks that all observed
cells agree and are strictly positive. `strict_subquery_disagrees` gives
the probabilities `3/8` and `7/16` for `Y=1` when only `A₂` is
set to zero.

`full_query_formula` proves equality between the paper's observational
ratio and the direct intervention on both treatments at every binary
assignment within each model. `full_query_agrees` verifies that the
intervention agrees across the two models.
`full_query_trace` and `strict_subquery_trace` exercise the Tian–Pearl
graph procedure starting from the factor on `{W,A₂,Y}`. It reaches the
target `{Y}` for the full query and an ancestor fixed point for target
`{W,Y}`. This replay concerns the source graph and the two constructed
models. Identification of the full query across all compatible models
uses the paper's argument.

## Fixed points and valid fixing orders

[FixedPointObstruction.lean](../../OpenCausalScience/Papers/Shpitser2023/FixedPointObstruction.lean)
formalizes a graphical step in Proposition 1. If every vertex of a
bidirected-connected set is an ancestor of a retained target within
that set, any fixing order that keeps the target also keeps the entire
set. Each extra vertex has a distinct target descendant in its current
district, even if the current graph still has other vertices.
`proper_fixed_point_blocks_target` proves that such a proper fixed
point makes the target unreachable. The declaration
`Figure1C.strict_subquery_target_not_reachable` applies it to
`{W,Y}` in the paper's four-vertex graph. The general implication from
a hedge to probability-level nonidentifiability is separate.

The [CGA fixture](https://github.com/snu-causality-lab/cga/blob/v0.2.0a1/tests/fixtures/papers/shpitser_2023_figure1c_hedge_counterexample.json)
checks the distinction between the two queries at the identification API.

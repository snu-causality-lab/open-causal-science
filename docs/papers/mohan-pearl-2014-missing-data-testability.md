# Mohan and Pearl (2014), testability with missing data

<!-- topic: Missing data -->

[AISTATS 2014, On the Testability of Models with Missing Data](https://proceedings.mlr.press/v33/mohan14.html)

## A test for binary independence

Theorem 3 asks whether a manifest law is compatible with independence between fully observed binary `X` and partially observed binary `Y`. In each row indexed by `X`, assign some of the missing mass to `Y = 0` and the rest to `Y = 1`. This gives an interval for the completed conditional probability of `Y = 0`. The endpoints come from assigning all the missing mass to either one or zero. [Theorem 3, pp. 647–648](https://proceedings.mlr.press/v33/mohan14.pdf#page=5)

[BinaryTestability.lean](../../OpenCausalScience/Papers/MohanPearl2014/BinaryTestability.lean) proves that a proposed conditional rate is achievable exactly when it lies inside the interval. For nonnegative manifest masses with both rows supported, `allows_independence_iff_overlap` proves that a compatible independent completion exists exactly when the two intervals overlap. The theorem concerns the existence of a compatible completion given exact cell masses. [Table 2 and Example 7](https://proceedings.mlr.press/v33/mohan14.pdf#page=6)

The Lean replay checks that Table 2's `P1` and `P2` each admit an independent completion. In `P3` the first row requires at least `100/110`, while the second permits at most `12/15`. The disjoint intervals refute independence for every compatible completion. The paper’s general direct-testability criterion in Theorem 1 remains a separate target.

## Holding the required responses fixed

[ComparisonWitnesses.lean](../../OpenCausalScience/Papers/MohanPearl2014/ComparisonWitnesses.lean)
checks the choice of a comparison variable in Theorem 1. CGA holds
fixed all response indicators needed to observe members of the three
independence sets, including the indicators of variables in the right
set. This restriction preserves the existence of a comparison variable.
If a candidate indicator is needed to reveal a true variable in the
right set, that true variable is itself a candidate. The Lean result
uses the disjoint roles of substantive variables and response indicators.

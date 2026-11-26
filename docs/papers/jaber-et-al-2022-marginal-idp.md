# Jaber et al. (2022), marginal identification in a PAG

<!-- topic: Identification -->

[Paper index](../paper-checks.md)

Example 3 of the May 2022 report R-86 illustrates Proposition 2 and
Algorithm 1 on Figure 3(a). It first removes the bucket
`{X₁,W}`, then removes `{X₂}`. The source simplifies the
result to `P(a)P(y,z | w,a)`. [R-86, Section 4.1](https://causalai.net/r86.pdf#page=6)

[Example3.lean](../../OpenCausalScience/Papers/JaberEtAl2022/Example3.lean)
computes possible descendants and possible c-component membership from the
figure's endpoint marks and visibility labels. The first bucket's
possible c-component contains `A,X₁,X₂,W`, and its possible
descendants are `X₁,W,Z,Y`. Their intersection is the bucket. After
removing it, `X₂` is isolated. Lean checks both instances of the
graphical test and obtains the denominator conditioning sets
`{A,X₂}` and `{A,Z,Y}`.

## Proposition 2's bucket quotient

[BucketQuotient.lean](../../OpenCausalScience/Papers/JaberEtAl2022/BucketQuotient.lean)
proves the probability calculation in Proposition 2, Equation (1).
The old kernel is a product of a normalized bucket mechanism and the
retained kernel indexed by the bucket intervention. The conditioning
variables have the same marginal for every such intervention.
`bucket_conditional_eq_mechanism` computes the mechanism by
marginalizing and normalizing the old table.
`bucket_quotient_recovers_kernel` divides it out on supported cells and
recovers the retained kernel at the chosen intervention. The proof that
the PAG condition implies these premises, and the general correctness and
completeness of Algorithm 1, remain separate. [R-86, Appendix D](https://causalai.net/r86.pdf#page=21)

The [CGA marginal IDP contract](https://github.com/snu-causality-lab/cga/blob/v0.2.0a1/docs/reference/PUBLISHED_IDENTIFICATION.md#equivalence-classes)
uses the possible-descendant test of this edition.

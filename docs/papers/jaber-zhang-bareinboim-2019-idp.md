# Jaber, Zhang and Bareinboim (2019), IDP

<!-- topic: Identification -->

[Paper index](../paper-checks.md)

## Figure 2 and Algorithm 1

Figure 2(a) asks for the joint effect of `X₁,X₂` on
`Y₁,…,Y₅`. The paper decomposes the target because neither intervention
bucket can be removed in the first call. The region of the seed
`{Y₃}` gives the split in Equation (6). [ICML 2019 proceedings, Figure 2 and Corollary 1](https://proceedings.mlr.press/v97/jaber19a/jaber19a.pdf#page=5) · [Worked example, §4.1](https://proceedings.mlr.press/v97/jaber19a/jaber19a.pdf#page=6)

[Figure2.lean](../../OpenCausalScience/Papers/JaberEtAl2019/Figure2.lean)
represents the published endpoint marks and the two marked visible
edges. It searches simple paths for the possible c-component and
circle-connected buckets of the induced sub-PAG.

- `initial_bucket_removals_blocked` checks both initial singleton
  intervention buckets against Algorithm 1, line 6.
- `corollary_regions` computes the two regions
  `{Y₂,Y₃,Y₄,Y₅}` and `{Y₁,Y₄,Y₅}`, with overlap `{Y₄,Y₅}`.
- `recursive_bucket_removals` computes one admissible sequence of
  removals for each of the three recursive queries. For the first
  region this is `Y₁,X₁,X₂`, as in §4.1.
- `districts_differ_across_representatives` checks the change from
  `{Y₂,Y₃}` to `{Y₂,Y₃,Y₄}` for the district of `Y₃` between
  the two causal diagrams in Figure 2(b–c).

## Corollary 1 and Equation (14)

`region_quotient_of_district_products` proves the cancellation in
Equation (5) from the four stated district products at a fixed cell.
The product of the two region cells divided by their intersection cell
gives the whole cell when the intersection has nonzero mass.
`figure2_expression` applies this calculation to the three regions.
With the cells identified by Equations (11)–(13), it yields the
ratio in Equation (14). The graphical derivation of those cell formulas,
the district products for every compatible diagram, and general IDP
soundness and completeness remain separate. [ICML 2019 proceedings, §4.1](https://proceedings.mlr.press/v97/jaber19a/jaber19a.pdf#page=7)

The [2022 paper record](jaber-et-al-2022-marginal-idp.md) covers the
later marginal IDP algorithm and its possible-descendant condition.

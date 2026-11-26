# Witte et al. (2020), efficient adjustment

<!-- topic: Adjustment -->
<!-- index-anchor: witte-et-al-2020-figure-2b -->
<!-- index-anchor: witte-et-al-2020-figure-2f -->

[Paper index](../paper-checks.md)

## The O-set in the forbidden projection

[ForbiddenProjection.lean](../../OpenCausalScience/Papers/WitteEtAl2020/ForbiddenProjection.lean) proves `o_set_iff_projected_parent`, the graph equality of [Proposition 10](https://jmlr.org/papers/volume21/20-175/20-175.pdf#page=10) for finite DAGs. Treatments and outcomes are disjoint, and every outcome descends from a treatment. Under these assumptions, the parents of causal nodes outside the forbidden set are exactly the retained parents of outcomes in the forbidden projection, after excluding treatments and outcomes. The proof uses the directed part of Definitions 4–5 and covers arbitrary treatment and outcome sets. The main reverse step starts a proper causal path at the last treatment on a directed prefix. The result concerns the graph construction. Adjustment validity and variance comparisons are separate results.

## Figure 2B

*On Efficient Adjustment in Causal Graphs*, JMLR 21(246), Figure 2B (p. 8) and the text immediately after Proposition 6 (p. 9). The publisher PDF has SHA-256 `76b259d4937132f22b76899a81cdbd0a37299276eaddc05453b9b62adc160733`. [Publication and PDF](https://jmlr.org/papers/v21/20-175.html)

The text includes panel B among the panels with a valid adjustment set. The drawing has `X₁ → V₁ ← V₂ → Y → X₂` and boxes `V₂`. With treatments `{X₁, X₂}` and outcome `Y`, the corrected conclusion is that panel B admits no valid adjustment set. The proper noncausal path `X₂ ← Y` has no interior vertex, so it remains open under every allowed conditioning set. The absence of directed treatment-to-outcome paths also puts the panel outside the descendant premise of Proposition 6.

[Figure2B.lean](../../OpenCausalScience/Papers/WitteEtAl2020/Figure2B.lean) proves the two directed reachability exclusions in `WitteFigure2B.noDirectedTreatmentToOutcome`. It checks all four candidates in `WitteFigure2B.candidateSetsFailToSeparate`. The mathematical conclusion about adjustment uses the graphical criterion with these checked premises. The CGA paper review recorded the discrepancy before this Lean check.

## Figure 2F

In panel F, Definition 5 removes `V₂` for the treatments `{X₁, X₂}` and outcome `Y`. Every directed path from `V₁` to `X₂` or `Y` visits the retained `X₁`. Definition 4 therefore gives the four projected arrows `V₁ → X₁`, `X₁ → X₂`, `X₁ → Y` and `X₂ → Y`, together with `X₂ ↔ Y`. [Definitions 4–5 and Figure 2F](https://jmlr.org/papers/volume21/20-175/20-175.pdf)

[Figure2F.lean](../../OpenCausalScience/Papers/WitteEtAl2020/Figure2F.lean) checks the complete edge relations in `WitteFigure2F.directedEdges` and `WitteFigure2F.bidirectedEdges`. It excludes the two additional arrows printed in the projection. The remaining `X₂ ↔ Y` and the original directed edge `X₂ → Y` give the paper's adjustment conclusion by Proposition 6. The CGA paper review recorded both the projection discrepancy and the adjustment conclusion before this Lean check.

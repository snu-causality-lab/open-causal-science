# Mohan, Pearl and Tian (2013), graphical inference with missing data

<!-- topic: Missing data -->

[NeurIPS 2013, Graphical Models for Inference with Missing Data](https://papers.neurips.cc/paper_files/paper/2013/hash/0ff8033cf9437c213ee13937b1c4c455-Abstract.html)

## Target joint recovery with separate response mechanisms

Theorem 2 concerns the joint distribution of the substantive variables. It assumes there are no arrows between response indicators and no latent parents of the indicators. Under these restrictions and complete-case positivity, the theorem characterizes recovery by the absence of direct self-censoring arrows. The paper uses `R = 0` for observed entries. [Theorem 2 and Equations (6)–(8)](https://proceedings.neurips.cc/paper/2013/file/0ff8033cf9437c213ee13937b1c4c455-Paper.pdf#page=6)

[JointRecovery.lean](../../OpenCausalScience/Papers/MohanEtAl2013/JointRecovery.lean) checks the sufficiency steps. `sink_indicator_parent_separation` proves that the indicator is d-separated from nonparents after conditioning on its parents in the graph with deterministic proxy leaves omitted. In particular, indicators of partially observed parents are nonparents of the response indicator. `response_ratio_eq` proves that summing over the other entries in the observed parent stratum preserves the shared response rate. `joint_cell_from_observed_responses` recovers a target cell from its complete-case mass and a product of these observed response rates. The finite rational proof takes the complete-case Markov factorization and supported stratum invariance as premises. The unrestricted necessity argument remains open in this companion. The [binary self-censoring example](nabi-et-al-2020-missing-data-full-law.md) checks the simplest obstruction separately.

## Recovery with cross-censoring

Figure 3(b) has arrows from `X` to `Y` and to the response indicator of `Y`, and from `Y` to the response indicator of `X`. [CrossCensoring.lean](../../OpenCausalScience/Papers/MohanEtAl2013/CrossCensoring.lean) checks the separating statements and the failure of the two unconditional separations. `recover_cross_censoring` proves Equation (5) for binary rational laws of this form on supported strata. A numerical example constructed on the published graph recovers all four target cells and shows how normalizing the complete cases can instead give a biased cell. [Example 5 and Equation (5)](https://proceedings.neurips.cc/paper/2013/file/0ff8033cf9437c213ee13937b1c4c455-Paper.pdf#page=6) · [Figure 3(b)](https://proceedings.neurips.cc/paper/2013/file/0ff8033cf9437c213ee13937b1c4c455-Paper.pdf#page=8)

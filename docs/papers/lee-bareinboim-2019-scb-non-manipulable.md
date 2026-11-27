# Lee and Bareinboim (2019), structural causal bandits with non-manipulable variables

<!-- topic: Causal decision making -->

[Paper index](../paper-checks.md)

> **Author correction** · [Proposition 3](#corrected-proposition-3) · A projected POMIS needs one witness on the original graph that preserves all its strict comparisons.

## Corrected Proposition 3

Let `G` be a finite causal diagram, let `Y` be a retained reward vertex, and let `H`
be the projection obtained by removing the non-manipulable vertices. For every
POMIS `X` of `H`, `preserves_pomis_witnesses` produces one finite SCM with diagram
`G` in which the best mean reward under `X` is strictly greater than under each
other feasible MIS. The comparison ranges over intervention sets avoiding the
removed vertices. `Model.best` maximizes the mean of a reward function `r(Y)` over
the finite arm assignments for each set. The 2018 witness uses rewards in `{0, 1}`.
[Proceedings](https://doi.org/10.1609/aaai.v33i01.33014164) ·
[September 19, 2026 correction](https://www.sanghacklee.me/ai-corrected/SCB2019_AI_corrected_2026-09-19.pdf) ·
[Lean theorem](../../analysis/OpenCausalScienceAnalysis/Decision/SCB2019Proposition3.lean)

The projection keeps removed indices isolated and proves that feasible MISs agree
across the original and projected diagrams. The POMIS witness uses the public 2018
construction, with independent private roots and roots shared by pairs. Restoring
one vertex routes the affected parent values and root values through its tuple
state. Retained domains are preserved. Declared inputs may be unused and the
restored domains can be chosen freely. Pointwise agreement of retained responses
and the product law on the same roots give equality of optimized rewards for every
retained intervention set. [Projection](../../analysis/OpenCausalScienceAnalysis/Decision/SCB2019Projection.lean) ·
[Witness selection](../../analysis/OpenCausalScienceAnalysis/Decision/SCB2019Witness.lean) ·
[Restoration](../../analysis/OpenCausalScienceAnalysis/Decision/SCB2019Restoration.lean)

## Obstruction to the published restoration statement

Eliminating `W` from `A ↔ W → B`, `A ↔ C`, and `B ↔ C` gives a bidirected
triangle. A common fair bit can produce three identical, nonconstant outputs
on the triangle. In the original graph's independent pairwise source blocks,
agreement on the product support forces the common output to be constant.
`no_common_fair_bit` proves this obstruction to restoring every projected model.
[Lean counterexample](../../OpenCausalScience/Papers/LeeBareinboim2019/RestorationCounterexample.lean) ·
[Evans, Example 6.6](https://arxiv.org/abs/1408.1809)

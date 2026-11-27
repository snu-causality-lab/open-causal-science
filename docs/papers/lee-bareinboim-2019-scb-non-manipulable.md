# Lee and Bareinboim (2019), structural causal bandits with non-manipulable variables

<!-- topic: Causal decision making -->

[Paper index](../paper-checks.md)

> **Author correction** · [Proposition 3 and Theorem 4](#pomis-equivalence) · The projected and constrained POMIS sets agree. Each projected POMIS uses one original-graph witness for all strict comparisons.

## POMIS equivalence

`constrained_pomis_eq_projected_pomis` proves Theorem 4 for finite SCMs with
freely chosen state spaces and possibly unused structural inputs. The set of
POMISs over feasible intervention sets of the original graph equals the set
of POMISs of the projected diagram. [Lean theorem](../../analysis/OpenCausalScienceAnalysis/Decision/SCB2019Theorem4.lean)

The forward projection in Proposition 2 substitutes a removed vertex's
equation into its children's equations, preserving the retained responses at
each exogenous assignment. After iterating the substitutions, Lean proves
equality of the expectation of every function of the retained responses for
each allowed arm. Indicator functions recover equality of the retained joint
interventional distributions. Independent roots may have any number of readers.
A one-point source shared by the children records the bidirected edges of a
removed common parent, even if that parent had no exogenous input. The source
has probability one, so it leaves the marginal law of the original roots intact.
[Forward mechanism](../../analysis/OpenCausalScienceAnalysis/Decision/SCB2019ForwardMechanism.lean) ·
[Joint expectations and best reward](../../analysis/OpenCausalScienceAnalysis/Decision/SCB2019ForwardProjection.lean)

Projection transports the 2018 border dominance inequality to every compatible
original SCM. A feasible set distinct from its projected border therefore has a
feasible competitor with at least its best reward. Corrected Proposition 3
supplies the witnesses in the reverse direction. [Public correction](https://www.sanghacklee.me/ai-corrected/SCB2019_AI_corrected_2026-09-19.pdf)

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

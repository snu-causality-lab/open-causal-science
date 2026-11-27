# Cho et al. (2026), decomposing conformal uncertainty

<!-- topic: Uncertainty quantification -->

[Paper index](../paper-checks.md)

The source is the public OpenReview paper *Decomposing Conformal Uncertainty:
Calibration- and Instance-Driven Feature Attribution*, listed as a NeurIPS 2026
poster. The PDF used for the checks has SHA-256
`410d13eef4ae3172fd069b9133051691e98ec8c5b1eaac807ce53f5d75de523c`.
[Public paper](https://openreview.net/forum?id=lZavBaxJ68) ·
[NeurIPS listing](https://neurips.cc/virtual/2026/poster/149998)

## Two-game decomposition

`shapley` implements Eq. (1) as a sum over the full powerset of the features
other than the feature being attributed. It uses real coalition payoffs and
the factorial coefficient `|S|! (d - |S| - 1)! / d!`. `shapley_linear` proves
linearity by distributing this coefficient over the two marginal increments.
`two_game_decomposition` is Theorem 1 in §4.1 and Appendix A.1. When the total
game at every coalition is the sum of its instance and calibration games,
the direct total allocation is the sum of their separate allocations.
[Lean module](../../analysis/OpenCausalScienceAnalysis/Uncertainty/ConformalShapley.lean) ·
[Theorem 1 experiment](https://github.com/snu-causality-lab/CP-SHAP/blob/d19c098229cd00a2905a3ea19e77cdd7cc32385b/experiments/cp_families/lacp_concrete/main.py#L142-L150)

## Width and masking

`transformed_width_decomposition` proves the allocation identity of
Proposition 1 using the same coalition to mask the test vector and every row
of the calibration matrix. The transformed width has to separate into a test
term and a calibration term on the masked inputs. `group_width_decomposition`
gives Proposition 2's allocation identity in a fixed group, using that group's
calibration summary and retaining the group during feature masking.

`cqr_attribution` derives the decomposition from the difference between the
corrected interval endpoints. `lacp_log_attribution` derives it from the
multiplicative width on the log scale when the scale and calibration quantile
are positive at every coalition. The scope is the finite attribution algebra
with supplied fitted endpoints, scales and calibration quantiles. The
implementation uses the same factorization in its LACP and Mondrian examples.
[LACP check](https://github.com/snu-causality-lab/CP-SHAP/blob/d19c098229cd00a2905a3ea19e77cdd7cc32385b/experiments/cp_families/lacp_concrete/main.py#L142-L150) ·
[Mondrian check](https://github.com/snu-causality-lab/CP-SHAP/blob/d19c098229cd00a2905a3ea19e77cdd7cc32385b/experiments/cp_families/mondrian_folktables/main.py#L184-L196)

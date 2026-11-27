# Choe, Kwon, Park and Lee (2026), Canonical Domain Reduction

<!-- topic: Counterfactual identification -->

[Paper index](../paper-checks.md)

This check uses the UAI 2026 proceedings version of *Canonical Domain Reduction
for Partial Counterfactual Identification*, PMLR 337, pp. 1302–1326. The
proceedings PDF has SHA-256
`dec09bde27157965030bd9e52d833f3401f9ba93d885ead23bf4c6de2d754cde`.
[Proceedings](https://proceedings.mlr.press/v337/choe26a.html)

## Proposition 3.1 — constraint-aware reduction preserves sharp bounds

Let `π` be a surjection from the full finite state space to the reduced one.
The objective coefficients and every information row must factor through
this same map. These are `c = Πᵀ c̃` and `M = M̃ Π` in the paper, using the
pushforward matrix `Π`. The feasible weights are nonnegative real vectors
with total mass one and satisfy the prescribed information equalities.

`linear_value_pushforward` proves the row identity used in Equations (12)–(13).
`pushforward_lift` recovers any reduced vector by placing the mass of each fiber
on one representative. `attainable_values_eq` proves that both feasible
problems realize exactly the same objective values, so every attainable value
on either side has a feasible witness on the other. `sharp_bounds_eq` gives
equality of the lower and upper bounds. The verification concerns the linear
program once the factorization premises hold. [Lean proof](../../analysis/OpenCausalScienceAnalysis/Identification/CanonicalDomainReduction.lean)

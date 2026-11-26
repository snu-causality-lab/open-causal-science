# Mohan and Pearl (2021), graphical models for processing missing data

<!-- topic: Missing data -->

[JASA 116(534), 1023–1037](https://doi.org/10.1080/01621459.2021.1874961) · [Authors' preprint, §3.1](https://arxiv.org/abs/1801.03583)

## Recovery by admissible factorization

Theorem 1 permits a different observation stratum for every factor of an ordered probability product. Each stratum observes the partially observed variables in the factor's outcome and conditioning sets. The factor equals its manifest version when its outcome is independent of the necessary response indicators given the conditioning variables and the stratum has positive probability. The theorem also permits sums of such products.

[OrderedFactorization.lean](../../OpenCausalScience/Papers/MohanPearl2021/OrderedFactorization.lean) checks these identities over rational event masses. It assumes the indicated independence, support, and the agreement of the proxies with the underlying variables on each factor's observation event. The checked theorem takes a decomposition as input and transports it to the manifest law factor by factor.

The Lean module checks the separations in Figure 4(a) needed by the factorization `P(Y | X) P(X)`, including the failure of the marginal separation of `Y` from its response indicator. It also formalizes the joint-cell identity in Corollary 2. Conditional on observed covariates, an independent complete-case response permits recovering the joint cell by multiplying a manifest conditional by the observed covariate marginal. [Theorem 1, Example 3, Figure 4(a) and Corollary 2](https://arxiv.org/pdf/1801.03583#page=15)

The article's cross-censoring example appears earlier in [Mohan, Pearl and Tian (2013), Figure 3(b)](mohan-et-al-2013-missing-data.md#recovery-with-cross-censoring).

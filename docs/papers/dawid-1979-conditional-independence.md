# Dawid (1979), conditional independence

<!-- topic: Graphical Markov models -->

Philip Dawid, *Conditional Independence in Statistical Theory*, Journal of the Royal Statistical Society Series B **41**(1), 1–15, followed by discussion. Section 4 derives rules for grouping, marginalizing, and conditioning observables. [Version of record](https://doi.org/10.1111/j.2517-6161.1979.tb01052.x) · [Article and discussion](https://people.csail.mit.edu/tdanford/discovering-causal-graphs-papers/dawid-79.pdf)

- [ConditionalIndependence.lean](../../OpenCausalScience/Probability/ConditionalIndependence.lean) defines conditional independence by cross-products of event masses and proves symmetry, decomposition, weak union, and contraction for finite nonnegative rational masses. An observable can include the conditioned variable without changing the independence statement, as in Lemma 4.1. The intersection theorem assumes positive mass for every pair of values of the two additional conditioning observables in each supported base stratum. It quantifies over all values of their declared Lean types. Zero-mass base strata impose no constraints.
- [Dawid1979/ConditionalIndependence.lean](../../OpenCausalScience/Papers/Dawid1979/ConditionalIndependence.lean) gives two finite examples. On diagonal support, both premises of intersection hold simultaneously and its conclusion fails. In a full-support noisy XOR distribution, each of two inputs is independent of the output, while their pair is dependent on it. Thus full support alone does not suffice for composition.

The checked scope is finite rational mass algebra. Sections 2–3 also discuss conditional independence statements involving fixed parameters. Dawid develops a formal treatment of those statements in [Conditional Independence for Statistical Operations (1980)](https://doi.org/10.1214/aos/1176345011). [Lean toolchain](../../lean-toolchain)

## Section 5 and the discussion

For the reverse implication in Section 5, Dawid combines no treatment effect for a fixed individual (5.1) and independence of the response from the individual given treatment and covariates (5.2). He uses the premise that each individual–treatment combination is conceptually possible to deduce response–treatment independence given covariates (5.3). For a finite observational-law analogue, positive mass for each individual–treatment cell within its covariate stratum suffices for intersection. The diagonal-support witness above shows why the two conditional independences alone do not suffice in that analogue. [Original paper, pp. 6–7](https://people.csail.mit.edu/tdanford/discovering-causal-graphs-papers/dawid-79.pdf#page=6)

In the journal discussion, Dawid accepted DeGroot's observation that performance was omitted from the graduate admissions example and proposed conditioning on performance in the no-bias criterion. [Author's reply, p. 30](https://people.csail.mit.edu/tdanford/discovering-causal-graphs-papers/dawid-79.pdf#page=30)

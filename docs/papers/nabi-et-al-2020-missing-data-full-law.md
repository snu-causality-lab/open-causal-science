# Nabi, Bhattacharya and Shpitser (2020), full-law identification with missing data

<!-- topic: Missing data -->

Theorems 1–2 characterize full-law identification in a missing-data DAG by
the absence of self-censoring and colluders, under response positivity.
Theorems 3–4 extend the criterion to missing-data ADMGs using colluding paths.
[ICML 2020, §§5–6](https://proceedings.mlr.press/v119/nabi20a.html)

## One binary variable with self-censoring

[The Lean companion](../../OpenCausalScience/Papers/NabiEtAl2020/SelfCensoring.lean)
checks the obstruction from the direct edge from the true variable to its
response indicator. The missingness graph has one true variable, one response
indicator and the deterministic proxy. The proxy equals the true variable when
the indicator is one and is missing otherwise.

`Law.factorizes` gives the two stochastic factors of this graph for any
strictly positive normalized binary table. `observed_eq_iff` gives the exact
conditions for two tables to have the same observed law. They agree on each
observed cell and on the total mass of the two missing cells.

The concrete pair has observed mass one quarter for either observed value and
one half for missingness. Its target probability of one is one half in the
balanced law and five eighths in the self-censoring law. All conditional
response cells exceed one quarter. `positive_self_censoring_counterpair`
checks both the difference in the full law and the difference in the target.
`no_universal_target_recovery` rules out a recovery function on the observed
law for this model. These two laws are a constructed instance of Theorem 2's
obstruction. The general colluder, colluding-path and odds-ratio results remain
open here.

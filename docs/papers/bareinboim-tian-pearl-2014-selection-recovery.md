# Bareinboim, Tian and Pearl (2014), recovery from selection bias

<!-- topic: Selection recovery -->

[Paper index](../paper-checks.md)

These checks use the July 2014 UCLA report R-425 containing the AAAI
paper, pp. 2410–2416. The selection variable indicates which units
were recorded, and an external margin, when available, comes from the
same target population. [AAAI proceedings](https://doi.org/10.1609/aaai.v28i1.9074) ·
[Technical report R-425](https://ftp.cs.ucla.edu/pub/stat_ser/r425.pdf)

## Recovery from a selected sample

Theorem 1 tests whether selection and outcome are d-separated given
the variables in the query's conditioning set. In
[SelectionCriterion.lean](../../OpenCausalScience/Papers/BareinboimTianPearl2014/SelectionCriterion.lean),
`passes_iff_no_active_path` proves that the mixed-graph separation
routine used for this check returns true exactly when there is no
active path. The source and the query use disjoint outcome,
conditioning and selection variables. CGA's
`recover_conditional_distribution` uses this test for the fixed
selection event supplied in the data.

[ConditionalRecovery.lean](../../OpenCausalScience/Papers/BareinboimTianPearl2014/ConditionalRecovery.lean)
proves the formula step. `conditional_from_selected_law` makes
explicit how conditioning the selected law on `X=x` gives the
population conditional on `X=x,S=s`.
`selected_conditional_eq_population` proves equality with the target
`P(y | x)` given the conditional independence and nonzero stratum
masses. The graph-implied independence and the general necessity
statement use the paper's causal-model assumptions.
[Theorem 1 and Lemma 1](https://ftp.cs.ucla.edu/pub/stat_ser/r425.pdf#page=3)

[Figures.lean](../../OpenCausalScience/Papers/BareinboimTianPearl2014/Figures.lean)
checks the five selection diagrams in Figure 1. Panels (c) and (e)
pass. Panels (a), (d) and (f) retain an active connection. For panel (d),
`outcome_dependent_selection_nonrecovery` builds two positive binary
factorizations on `X → Y → S`. The entire selected `X,Y` table
agrees although the population `P(Y=1 | X=x)` is `1/2` in one
and `3/4` in the other, at either value of `x`.
[Figure 1](https://ftp.cs.ucla.edu/pub/stat_ser/r425.pdf#page=2)

## Recovery with a population margin

`recover_with_population_strata` proves Equation (4) of Theorem 2.
It partitions the target by covariate assignments, uses the selected
outcome conditional within each stratum, and weights by the
population `P(c | x)`. The finite rational proof assumes an
exhaustive, duplicate-free list of strata and each used stratum has
nonzero population and selected mass.

`exists_external_separator_iff` proves the graphical equivalence in
Theorem 3 for finite DAGs. If any allowed set drawn from the common
measured variables separates outcome and selection, the common
measured ancestors of outcome, selection and the required conditioning
variables do so. The proof maps a path in the unblocked ancestral
moral graph for the canonical set to a path for any candidate. Figure
2 checks that `{W₁,W₂}` and `{W₂,Z₃}` pass when added to
`X`, while `{W₂,Z₁,Z₂}` fails. [Theorems 2–3 and Figure 2](https://ftp.cs.ucla.edu/pub/stat_ser/r425.pdf#page=4)

## Selection-backdoor formula

`selection_backdoor_formula` proves the final substitution in
Theorem 5, Equation (9). Given the population adjustment identity and
supported conditional independence from selection within each
`X,Z` stratum, it replaces the observational conditional by the
one in the selected sample. The weights are the population `P(z)`.
The graph-to-adjustment step is a premise of the Lean statement.
[Theorem 5](https://ftp.cs.ucla.edu/pub/stat_ser/r425.pdf#page=6)

# Correa, Tian and Bareinboim (2018), adjustment under confounding and selection

<!-- topic: Selection recovery -->

[Paper index](../paper-checks.md)

An adjustment pair divides the covariates into an externally measured
subset and a remainder. Equation (6) averages the outcome conditional in
the selected sample against the remainder's conditional distribution
in that sample and the external subset's marginal distribution in the
same population. The Lean statements use the AAAI paper and its
Technical Report R-29, with the report's PDF page numbering.
[Proceedings](https://ojs.aaai.org/index.php/AAAI/article/view/12125) ·
[R-29, Definitions 7–8 and equations (5)–(6)](https://causalai.net/r29.pdf#page=4)

## Graphical criterion

[Criterion.lean](../../OpenCausalScience/Papers/CorreaTianBareinboim2018/Criterion.lean)
implements Definition 9. `proper_backdoor_deletes_iff` proves that
exactly the first directed arrows of proper causal paths are deleted.
`forbidden_iff_through_causal_vertex` proves that searching from those
first children finds the descendants of all non-treatment vertices on
those paths. The search stays outside treatment, as does the descendant
operation in the graph with incoming treatment arrows removed.
`valid_iff_admissible` proves that the Boolean checker implements
Definition 9's two marked-path separation tests and forbidden set.
The pair must also put its population part inside both the adjustment
set and the externally measured variables. This agrees with the check
used by the public CGA API. [R-29, Definition 9](https://causalai.net/r29.pdf#page=5) ·
[CGA selection recovery](https://github.com/snu-causality-lab/cga/blob/v0.2.0a1/docs/reference/PUBLISHED_IDENTIFICATION.md#selection-recovery)

[Figure2.lean](../../OpenCausalScience/Papers/CorreaTianBareinboim2018/Figure2.lean)
checks the original seven-vertex ADMG with joint treatment `{X₁,X₂}`.
The pair `({Z₁,Z₂,Z₃}, {Z₂})` passes. Adding `Z₁` to the population
part fails even when all three covariates are externally measured.
The selected-only and all-adjustment-measured forms fail for every
candidate adjustment set on this graph. [R-29, Figure 2](https://causalai.net/r29.pdf#page=4)

[JointTreatment.lean](../../OpenCausalScience/Papers/CorreaTianBareinboim2018/JointTreatment.lean)
distinguishes the proper-path reading from the literal phrase “all
non-causal paths” in Definition 8(b). With treatment `{A,B}`, the path
`B ← A → Y` is active given `S` but crosses another treatment vertex.
Definition 9 accepts the empty pair. The proof of Proposition 3 also
restricts attention to proper paths by restarting at another treatment
vertex when encountered. [R-29, Proposition 3](https://causalai.net/r29.pdf#page=20) ·
[CGA regression](https://github.com/snu-causality-lab/cga/blob/v0.2.0a1/tests/python/test_selection_recovery.py)

## Finite recovery formula

[Recovery.lean](../../OpenCausalScience/Papers/CorreaTianBareinboim2018/Recovery.lean)
evaluates equation (6) from a finite rational selected joint table and
the population marginal. The supplied assignment lists index the
partitions to sum over. Positive selected denominator masses suffice
for the supported evaluator. A common positive scale of the selected
table cancels from both conditionals, so a selection rate is unnecessary.
The empty population subset and the full external adjustment set give
equations (2) and (3), respectively.

[Figure2Recovery.lean](../../OpenCausalScience/Papers/CorreaTianBareinboim2018/Figure2Recovery.lean)
proves equation (5) using the appendix's total-probability and exchange
identities. It computes both selected conditional weights from the same
joint table and combines them using the chain rule. The relevant
conditional identities and support conditions are explicit premises.
Theorem 1's probability-level criterion for all compatible models
and Algorithm 1's polynomial-delay listing analysis belong to the
source proof. [R-29, Appendix equations (8)–(16)](https://causalai.net/r29.pdf#page=9)

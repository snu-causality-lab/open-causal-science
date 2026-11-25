# Kim, Cho and Lee (2026), Beyond Bounds

<!-- topic: Counterfactual fairness -->

[Paper index](../paper-checks.md)

These checks use the UAI 2026 proceedings version of *Beyond Bounds:
Quantifying the Probability of Counterfactual Fairness*, PMLR 337, pp. 2994–3011.
The proceedings PDF has SHA-256
`818f591954d5ca45f2d7dc6635fdf20272ae748efd10b110069253bd7d3d4da2`.
[Proceedings and PDF](https://proceedings.mlr.press/v337/kim26b.html)

## Lemma 2 — canonical hull

[CanonicalHull.lean](../../analysis/KimEtAl2026BeyondBounds/CanonicalHull.lean)
proves equality with the bounded linear system of Appendix B.1 under its
Q-factor identification and product assumptions. The finite response blocks
are probability vectors. [PrefixCanonicalHull.lean](../../analysis/KimEtAl2026BeyondBounds/PrefixCanonicalHull.lean)
proves a second characterization using observed prefix masses. Each equation
compares successive prefix masses after cross-multiplication in the component
that owns the next observed vertex. The constraints are linear in the response
weights and also cover observations with zero probability.
[SCMPrefixHull.lean](../../analysis/KimEtAl2026BeyondBounds/SCMPrefixHull.lean)
derives this system from the ranked structural equations. With a parent-before
enumeration and normalized observational probabilities,
`TopologicalOrder.scm_canonical_hull_eq_linear_constraints` proves equality
between the finite linear system and compatibility with the full observed
distribution. The corresponding hull is convex and bounded.

## Proposition 3 — reduced counterfactual effect

[ReducedCE.lean](../../analysis/KimEtAl2026BeyondBounds/ReducedCE.lean)
represents finite ranked structural models with independently distributed
exogenous blocks, and includes the canonical response-table specialization.
The maximal C-component membership is supplied. For a fixed observation law
and a positive factual context mass, `RankedSCM.exists_measurable_reduced_effect`
constructs the measurable counterfactual-minus-factual effect from only blocks
containing a strict descendant of the intervened variable. The proof checks the
joint factual and intervened output event using shared noise. It eliminates the
omitted block factors using the observational law, including when individual
complete assignments have probability zero.

## Lemma 4 — prior probability

[PriorProbability.lean](../../analysis/KimEtAl2026BeyondBounds/PriorProbability.lean)
proves that a reduced prior's probability of an interval event is its integral
of one over that event. It also proves equality with the full-space event when
the reduced prior is the pushforward of the full prior. For a finite family of
supported queries, the same reasoning checks the joint tolerance-fairness event
from Definition 5. These identities are about the chosen prior. The paper's
Hit-and-Run implementation and simulation estimates are separate.

## Check the proofs

From the optional `analysis/` package, run `lake build` and
`lake env lean FocusedAxioms.lean` with Lean and Mathlib v4.36.0.

# Park and Lee (2026), transportability for structural causal bandits

<!-- topic: Causal decision making -->

[Paper index](../paper-checks.md)

The checks use *On Transportability for Structural Causal Bandits*, UAI 2026,
PMLR 337, pp. 5266–5288. The proceedings PDF has SHA-256
`0facafc7f1d18a95ad139eedd029baf55bfb9cca5e371735988e99cc96b3582d`.
[Proceedings and PDF](https://proceedings.mlr.press/v337/park26a.html)

## Partial transportability bounds

`nested_factor_bounds` proves the pointwise lower bound of Appendix C.1 and
Eq. (47) for finite recursive SCMs. For nested sets `A ⊆ D`, let `E` be
the event that the response on `A` equals the assigned value when the
complement of `A` is fixed. Let `F` be the event that the response on
`D \ A` equals the assigned value when the complement of `D` is fixed.
On `F` the two interventions have identical responses by composition.
Consequently `Q[D]` is the probability of `E ∧ F`. Its marginal over `A`
is the probability of `F`. Monotonicity gives the lower bound on `Q[A]`,
and the probability of the complement of `F` gives the upper bound.
[Lean module](../../analysis/OpenCausalScienceAnalysis/Decision/SCB2026Transport.lean)

`partial_transport_bounds` proves Eqs. (10)–(11) of Proposition 1. It
sums the bounds on `Q[C′]` and applies the ancestral marginalization
identity to `C ⊆ C′ ⊆ D`. The theorem takes an ancestral `C` in the
induced graph on `C′` and the source–target factor equality of Eq. (27)
as premises. The expressions give computable bounds when the source
factor `Q[D]` has been identified.
[Ancestral marginalization](../../analysis/OpenCausalScienceAnalysis/Identification/QFactor.lean)

## Minimal intervention sets

`projected_pomis_is_original_mis` checks Proposition 2 in its
latent-projection form. The checked equality of constrained and
projected POMISs converts a projected POMIS to a constrained POMIS,
whose intervention set is minimal in the original diagram.
[Projection equivalence](lee-bareinboim-2019-scb-non-manipulable.md#pomis-equivalence)

# Malinsky, Shpitser and Richardson (2019), conditional path-specific effects

<!-- topic: Path-specific effects -->

[Paper index](../paper-checks.md)

Algorithm 1 applies the potential-outcomes form of Rule 2 in the
extended graph. It identifies the remaining joint path-specific
distribution and divides by the mass of the remaining evidence.
Proposition 10 gives the extension from edge-consistent path-specific
responses to standard interventions on the added treatment copies.
[Proceedings, Proposition 10 and §6](https://proceedings.mlr.press/v89/malinsky19b/malinsky19b.pdf#page=8)

## Deterministic treatment copies

[ExtendedGraph.lean](../../OpenCausalScience/Papers/MalinskyEtAl2019/ExtendedGraph.lean)
checks the finite binary SCM step behind the construction in §5. An
unclamped identity copy evaluates to its original parent's response.
`edge_response_via_node_copies` proves that when the expanded DAG's
mechanisms route each incoming input through its specified original
parent or deterministic copy, clamping the copies gives the same unit
responses as setting the original edges. The proof keeps the same
original noise and assumes the stated routing and structural equations.
Proposition 10 also compares identifiability across graphs. The verified
result is the unit response equality.

## Figure 1

[Figure1.lean](../../OpenCausalScience/Papers/MalinskyEtAl2019/Figure1.lean)
checks both latent-projection graphs and the tested exchange of `C`.
The two copies of `A` are fixed, and the bidirected `C ↔ Y` survives
the Rule 2 cut in both panels. For the reduced joint on `{C,Y}`,
the paths `A → M → Y` and `A → Y` assign different values to `A`.
In panel (a) the first children `M,Y` share the district `{C,M,Y}`.
For the marginal outcome `Y`, `C` drops out of the ancestor set after
removing `A`, and the recanting district disappears. In panel (b)
`C → M` replaces `C ↔ M`, and `M,Y` belong to different districts for
both queries. `recanting_trace` uses the verified
[Shpitser district criterion](../../OpenCausalScience/Papers/Shpitser2013/RecantingDistrict.lean).
[Proceedings, Figure 1](https://proceedings.mlr.press/v89/malinsky19b/malinsky19b.pdf#page=3)

The same file constructs two binary SCMs for panel (a). Let `U,V` be
independent fair bits for the two latent roots, and let the three
private noises also be independent fair bits. In both models
`C = U xor V`, the baseline mediator is `U`, and the active mediator
is its private noise. The active outcome equals `V xor M` in the
first model and its complement in the second. The baseline outcome
uses private noise. Every observed cell has probability `1/16` in
both models. The marginal nested outcome has mass `1/2` in both,
while the nested outcome's probability of one given `C = 1` is
respectively one and zero. The conditioning event has mass `1/2` in
both models.

[Figure1BFormula.lean](../../OpenCausalScience/Papers/MalinskyEtAl2019/Figure1BFormula.lean)
checks panel (b)'s conditional functional under the joint factorization
that shares the `C,Y` latent factor and keeps a separate mediator factor.
`conditional_path_formula` checks that the normalized path-specific
joint equals the sum over `m` of `p(y | m,a,c) p(m | a′,c)` on supported
parent cells. The joint factorization is a premise of this check.

## Normalization

[Normalize.lean](../../OpenCausalScience/Papers/MalinskyEtAl2019/Normalize.lean)
proves the normalization in Algorithm 1, line 2, for finite weighted
atoms and arbitrary finite outcome values. The conditions supply an
identified reduced joint and positive mass for the remaining evidence.
The success and failure traces above concern Figure 1. The general
PS-IDC completeness theorem requires separate results.

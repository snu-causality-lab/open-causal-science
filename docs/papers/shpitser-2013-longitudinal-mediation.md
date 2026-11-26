# Shpitser (2013), recanting districts in longitudinal mediation

<!-- topic: Path-specific effects -->

[Paper index](../paper-checks.md)

Definition 2 restricts the ADMG to the non-treatment ancestors of the
outcome along paths avoiding treatment. A district is recanting if the
same treatment has a selected proper path and an excluded proper
path to the outcome, with both first successors in that district.
The first successors may be the same vertex. A proper path encounters
a treatment only at its start. [Cognitive Science 37, Definition 2](https://doi.org/10.1111/cogs.12058)

[RecantingDistrict.lean](../../OpenCausalScience/Papers/Shpitser2013/RecantingDistrict.lean)
proves `mem_ancestralRegion_iff` for the directed reachability used to
build the region. The Boolean checker searches for paths from each
treatment, with membership in the selected set supplied by the caller.
`mem_suffixes_iff` proves completeness of the finite directed suffix
search. `recants_eq_true_iff` proves that the checker returns true
exactly for Definition 2 on finite ADMGs, including bows. It matches
paths using the first successor and the full continuation.

## Figures 4 and 5

[LongitudinalExamples.lean](../../OpenCausalScience/Papers/Shpitser2013/LongitudinalExamples.lean)
uses the directed and bidirected edges shown in the three panels.
In each panel the ancestor region is `{L₁,M₁,L₂,M₂,Y}`.

| Panel | Lean result |
| --- | --- |
| Figure 4 | The green paths have no recanting district. |
| Figure 5(a) | The added `L₂ ↔ M₂` places the first successors of `A₁ → M₂ → Y` and `A₁ → L₂ → Y` in `{L₁,L₂,M₂,Y}`. The first path is selected and the second is excluded. |
| Figure 5(b) | The added `M₁ → L₂` gives `A₀ → M₁ → Y` a proper excluded counterpart `A₀ → M₁ → L₂ → Y`. Both start through the singleton district `{M₁}`. |

[Author preprint, Figures 4–5](https://arxiv.org/pdf/1205.0241#page=41)

The paper's Theorem 3 connects the absence of a recanting district to
representation in terms of interventional densities. When that
condition holds, Theorem 4 connects identification from observations
to standard ID for the total effect. The Lean result here checks the
graphical criterion and its examples. The interventional density
formula and the probability-level conclusions come from the paper.
[Journal article, Theorems 3–4](https://onlinelibrary.wiley.com/doi/pdfdirect/10.1111/cogs.12058)

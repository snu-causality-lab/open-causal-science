# Correa, Tian and Bareinboim (2019), causal identification under selection

<!-- topic: Selection recovery -->

[Paper index](../paper-checks.md)

These checks use the AAAI paper and its technical report R-38,
November 2018, SHA-256
`035d09019e49a061a2e1a2e4279bde2745ebc79dced42f0ba341225d8be75a60`.
The external-data setting supplies a complete selected joint
`P(V | S=1)` and one unbiased joint margin from the same population.
[AAAI proceedings](https://ojs.aaai.org/index.php/AAAI/article/view/4125) ·
[Technical report R-38](https://causalai.net/r38.pdf)

## IDSB and the external population margin

[PopulationMargin.lean](../../OpenCausalScience/Papers/CorreaTianBareinboim2019/PopulationMargin.lean)
proves Lemma 1's substitution of a selected conditional and a
population margin. At a supported cell, equality of the conditional
shape gives equality of the reconstructed cell and the true
population cell. The reconstruction is undefined when the selected
denominator is unsupported.

[HybridDistrict.lean](../../OpenCausalScience/Papers/CorreaTianBareinboim2019/HybridDistrict.lean)
checks the eligibility test in Theorem 3. Every vertex of an eligible
district that is ancestral to the selection district, and every
current parent of such a vertex, is present in the available source.
The closed child set includes the unavailable vertices themselves.
`hybrid_factor_eq` proves the product in equation (6) from the
corresponding local prefix identities and support. It chooses the
population prefix inside the selection ancestry and the selected
prefix outside it. The graph-to-kernel implications for those
prefix identities are premises of this product check.
[R-38, Lemma 1 and Theorem 3](https://causalai.net/r38.pdf#page=4)

## Figures 2 and 3

[GraphCases.lean](../../OpenCausalScience/Papers/CorreaTianBareinboim2019/GraphCases.lean)
checks the population extension and district steps in all three
examples.

- Figure 2(a) expands the external margin on `Z` to `{Z,X,Y}`
  and checks that the selected prefixes recover the districts of
  `X` and `Y`. The target ancestral graph retains `R,Z,Y`
  before separately summing the first two coordinates.
- Figure 2(b) permits ordinary `Identify` on `{W₁,X,Y}`
  once the population joint is recovered. Lean checks that no
  adjustment pair works with either advertised margin.
  [Figure2B.lean](../../OpenCausalScience/Papers/CorreaTianBareinboim2019/Figure2B.lean)
  proves equation (23) on finite rational product-noise models of
  the figure. At fixed `W₂`, each selected conditional cell
  reweighted by `P(W₁)` gives the corresponding primitive cell
  on that `W₁` stratum. The ratio is taken after summing the strata,
  and equals the response under `do(X)`.
- Figure 3(a) checks the population extension from
  `{V₂,V₃,V₆}` and the post-intervention ancestor districts.
  The Figure 4 trace checks which districts the external-margin
  test makes available for division and which vertices are removed
  by the two ancestral restrictions.

These examples exercise both direct use of a population projection
and the RCE reduction. The general IDSB soundness theorem and
full latent-projection interface are separate results.
[R-38, Figures 2–4 and equation (23)](https://causalai.net/r38.pdf#page=7)

## Where the selected-only RC procedure stops

The independent [public CGA fixture](https://github.com/snu-causality-lab/cga/blob/v0.2.0a1/tests/fixtures/papers/correa_tian_bareinboim_2019_rc.json)
uses `W → X → Y`, `A → S`, `B → S`, `W ↔ Y`, `W ↔ A`,
and `X ↔ B`. Lean checks the original RC plan on this graph.
Its target district is `{Y}`, every vertex is an ancestor of
`Y` or `S` in the original graph, and every original district
meets the ancestors of `S`. The plan stops at line 3.

The same graph satisfies the
[generalized adjustment criterion](correa-tian-bareinboim-2018-selection-adjustment.md)
with adjustment `{W,A}` and an empty external adjustment set.
The published adjustment result therefore gives
`Σ_{w,a} P(y | x,w,a,S=1) P(w,a | S=1)` on supported cells.
Lean also checks the relevant graphical separation both before and
after conditioning on `A`. The two routes give a counterexample to
the necessity direction of the selected-only claim in Theorem 2.
[R-38, Algorithm 1 and Theorem 2](https://causalai.net/r38.pdf#page=3)

In Appendix B's second case, the directed path from `W` to the
target is `W → X → Y` in this graph. The proper back-door graph
deletes `X → Y`. Its remaining `Y ↔ W ↔ A → S` path has a closed
collider at `W`. Lean checks separation of `Y` and `S` in that graph,
so Theorem 1's antecedent is false in this example.
[R-38, Appendix B](https://causalai.net/r38.pdf#page=12)

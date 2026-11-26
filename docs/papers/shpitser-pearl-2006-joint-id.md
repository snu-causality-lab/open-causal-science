# Shpitser and Pearl (2006), joint interventional identification

<!-- topic: Identification -->

[Paper index](../paper-checks.md)

## Lemma 6 and line 3 of ID

Compute the ancestors of the outcome set after deleting arrows into the
original intervention targets. Lemma 6 lets line 3 of ID intervene
additionally on every remaining nonancestor, at arbitrary values,
without changing the distribution of the outcomes. [AAAI 2006 proceedings, p. 1224](https://cdn.aaai.org/AAAI/2006/AAAI06-191.pdf#page=6)

[Lemma6.lean](../../OpenCausalScience/Papers/ShpitserPearl2006/Lemma6.lean)
uses the ranked binary structural model from
[Tian and Pearl's ancestral marginalization](tian-pearl-2003-q-decomposition.md#ancestral-marginalization-and-the-product-of-c-factors).
It defines ancestry by directed reachability with the original interventions
applied. The source intervenes on observed nonancestors in its causal diagram.
Lean gives a unit-level statement on an explicit DAG, so its retained outcome
event is invariant to fixing any still-free nonancestors, including latent ones
if present in that DAG.

- `extra_actions_on_free_vertices` characterizes exactly which formerly free
  vertices receive the new clamps. `original_action_preserved` holds for
  every formerly clamped vertex.
- `nonancestor_actions_preserve_response` proves equality on every exogenous
  unit for each outcome coordinate disjoint from the original intervention.
- `nonancestor_actions_preserve_mass` lifts this equality to the outcome
  distribution under the same finite rational exogenous law.
- `nonancestor_marginal_equals_extra_action` also sums an exhaustive,
  duplicate-free partition of cells in the old regime.

The proof checks line 3 for this finite model. The identification recursion,
district extraction, and its failure criterion require additional results.

## The hedge criterion

The author's 2023 note gives a counterexample to the arbitrary-subquery
condition in AAAI Corollary 3. Proposition 1 gives the criterion for the
exact input query. The note retains the soundness and completeness of ID
and credits Ema Perkovic for bringing the counterexample to the author's
attention. [Public correction, arXiv:2307.03750v1, §§3–4](https://arxiv.org/pdf/2307.03750v1#page=7)

The [2023 paper record](shpitser-2023-id-failure.md) checks the example
and the graphical obstruction to a fixing order. The separately published
[conditional identification paper](shpitser-pearl-2006-conditional-idc.md)
uses the earlier hedge criterion in its Corollary 2.

# Mohan and Pearl (2018), consistent estimation with missing data

<!-- topic: Missing data -->

[Paper index](../paper-checks.md)

> **Verified discrepancy** · [Example 2, conditional independence](#conditioning-on-the-response-collider) · The stated independence conditions on a collider in Figure 1(b). The same page gives the separation needed for the response ratio.

[PGM 2018 proceedings](https://proceedings.mlr.press/v72/mohan18a.html) · [Proceedings PDF](https://proceedings.mlr.press/v72/mohan18a/mohan18a.pdf)

## Proxy recovery in a supported stratum

[ConditionalRecovery.lean](../../OpenCausalScience/Papers/MohanPearl2018/ConditionalRecovery.lean) formalizes the deterministic proxy in Equation (1). A recorded value agrees with the underlying value on the observed response event, denoted by `R = 0` in the paper. `proxy_conditional_recovers_target` proves equality between the manifest and target conditionals given the separation-induced independence and nonzero stratum masses. The graph in Figure 1(a) gives this separation after conditioning on `Y`. The replay recovers the joint masses `1/3` and `1/6` for the two values of `X` in each `Y` stratum. [Figure 1(a), Example 1 and Tables 1–2](https://proceedings.mlr.press/v72/mohan18a/mohan18a.pdf#page=3)

## Conditioning on the response collider

The first paragraph on page 288 of Example 2 uses independence of `R_X` and `X` given `Y, R_Y`. In Figure 1(b), conditioning on `R_Y` opens the collider path `R_X → R_Y ← X`. Lean checks the active path and a positive rational factorization of that graph that violates the printed independence even at the observed response value of `R_Y`.

The second bullet on the same page uses independence of `R_Y` and `Y` given `X, R_X`, which does follow from Figure 1(b). `response_rate_from_observed_x` uses it to read the response rate from the manifest data. For positive response rates, `conditional_from_complete_cases` divides the complete-case cells at fixed `Y` by the observed conditional response rate of `Y` and normalizes across `X`. The remaining response factor for `X` depends only on `Y` and cancels. This checks the illustrated conditional recovery. [Figure 1(b)](https://proceedings.mlr.press/v72/mohan18a/mohan18a.pdf#page=2) · [Example 2, pp. 287–288](https://proceedings.mlr.press/v72/mohan18a/mohan18a.pdf#page=4)

## What complete-case selection retains

[SelectionComparison.lean](../../OpenCausalScience/Papers/MohanPearl2018/SelectionComparison.lean)
connects Figure 1(a) to [selection recovery](bareinboim-tian-pearl-2014-selection-recovery.md).
Under the graph's conditional independence and support, complete cases
give the population conditional of the partly observed variable within
the fully observed stratum. Multiplying it by the population stratum
margin gives the joint cell. Here that margin is available from all
manifest rows, including rows with a missing proxy.

Two positive binary models constructed for this comparison agree on
every complete-case mass, even before normalization, while their
population joint cells differ. The models also differ in their
observed incomplete-case rows. Lean verifies that the manifest
recovers the joint cell in both models and that no function of just
the complete-case masses gives that joint cell in both. This example
shows the role of the information retained outside the selected sample.

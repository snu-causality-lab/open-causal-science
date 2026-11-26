# Akbari, Etesami and Kiyavash (2025), optimal experiment design

<!-- topic: Experimental design -->

[Paper index](../paper-checks.md)

> **Verified discrepancy** · [Definition 5 and Algorithm 1](#hedge-hull-with-no-proper-hedge) · The algorithm returns the target when the union of proper hedges is empty.

[JMLR 26(28), 2025](https://jmlr.org/papers/v26/22-1516.html) extends the authors’ [ICML 2022 paper](https://proceedings.mlr.press/v162/akbari22a.html). This record follows the JMLR numbering.

## Single intervention and hitting sets

[HedgeHull.lean](../../OpenCausalScience/Papers/AkbariEtAl2025/HedgeHull.lean) uses Definition 2 for a target set `S` that induces one district. A proper hedge contains `S`, is connected by bidirected edges, and consists entirely of ancestors of `S` within its own induced graph. The Lean district check uses a root chosen in `S` and inherits the finite walk semantics from the [Tian–Pearl recurrence](tian-pearl-2003-q-decomposition.md).

`no_hedge_after_removal_iff_hits_every_hedge` proves that deleting an intervention set disjoint from `S` leaves no proper hedge if and only if the intervention meets every hedge outside `S`. `minimum_removal_iff_minimum_hitting_set` lifts that equivalence to all minimizers of a shared cost function over admissible interventions. The probability-level statement that `Q[S]` is identifiable from the intervention regime exactly when the induced graph has no hedge is the criterion used in §3.1. The Lean statement checks the graph and optimization steps in Lemma 3. [Definition 2](https://jmlr.org/papers/volume26/22-1516/22-1516.pdf#page=6) · [Lemma 3](https://jmlr.org/papers/volume26/22-1516/22-1516.pdf#page=9)

## Hedge hull with no proper hedge

`hedgeHull` alternates retaining the district of `S` and the ancestors of `S` within that district. `hedge_hull_fixed` proves that the result has reached a fixed point within a number of strict reductions bounded by the input length. `mem_hedge_hull_iff` proves that a vertex survives exactly when it belongs to `S` or to a proper hedge. `no_hedge_iff_hull_subset_target` checks the stopping test used in the intervention algorithms. The Lean implementation uses the existing bounded reachability routines. Lemma 6’s DFS running-time claim concerns a different implementation of the reachability steps.

Definition 5 describes the hull as a union of hedges, while Definition 2 requires the hedge to properly contain `S`. If there are no proper hedges, the literal union is empty and Algorithm 1 returns `S`. The verified identity is `S` union all proper hedges. It agrees with Algorithm 1 and with the authors’ stopping condition `H ≠ S` in Algorithm 10. [Definition 5 and Algorithm 1](https://jmlr.org/papers/volume26/22-1516/22-1516.pdf#page=10) · [Algorithm 10](https://jmlr.org/papers/volume26/22-1516/22-1516.pdf#page=49)

## Running example

[Figures2And3.lean](../../OpenCausalScience/Papers/AkbariEtAl2025/Figures2And3.lean) transcribes Figure 2(a). `figure2_ancestors` checks that removing `x` leaves the ancestors of `{s₁,s₂}` equal to `{v₁,v₂,s₁,s₂}`. For the `Q[{s₁,s₂}]` example, `figure3_hedges` checks the two depicted hedges and `figure3_hitting_iff_v2` proves that every hitting set contains `v₂`. `figure3_singleton_optimum` proves that `{v₂}` is optimal for any cost monotone under inclusion, which includes the paper’s additive nonnegative intervention costs. After deleting `v₂`, `figure3_empty_union_case` checks the empty-union case on the same graph. [Figures 2–3](https://jmlr.org/papers/volume26/22-1516/22-1516.pdf#page=5) · [Lemma 3 example](https://jmlr.org/papers/volume26/22-1516/22-1516.pdf#page=9)

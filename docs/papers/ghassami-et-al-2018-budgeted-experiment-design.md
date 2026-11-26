# Ghassami, Salehkaleybar, Kiyavash and Bareinboim (2018), budgeted experiment design

<!-- topic: Experimental design -->

[Paper index](../paper-checks.md)

> **Verified discrepancy** · [Lemma 1, inequality direction](#the-printed-inequality) · The main text reverses the inequality. Supplementary Appendix B proves the increasing direction.

The paper assumes an observational Markov equivalence class is known
and chooses a set of separate single-vertex experiments. Equation (1)
averages the number of newly oriented edges over the DAGs in the
observational class. [ICML proceedings, pp. 1724–1733](https://proceedings.mlr.press/v80/ghassami18a.html)

## The printed inequality

For `I₁ ⊆ I₂`, the main text prints `D(I₂) ≤ D(I₁)` while
describing the objective as increasing. The authors' supplementary
proof establishes `D(I₁) ≤ D(I₂)`. A graph consisting of one undirected
observational edge has two candidate orientations. An empty design
resolves zero edges. Randomizing either endpoint in its own experiment
resolves one edge for either true orientation.
[Main paper, Lemma 1](https://proceedings.mlr.press/v80/ghassami18a/ghassami18a.pdf#page=4) ·
[Supplementary Appendix B](https://proceedings.mlr.press/v80/ghassami18a/ghassami18a-supp.pdf)

## Direction counts from compatible DAGs

[BudgetedOrientation.lean](../../OpenCausalScience/Papers/GhassamiEtAl2018/BudgetedOrientation.lean)
uses the [cut-signature criterion](hauser-buhlmann-2012-interventional-equivalence.md)
to retain candidate DAGs. A true arrow counts when another
observationally equivalent DAG can reverse it and every DAG compatible
with the selected regimes agrees on its direction. Adding experiments
can only remove candidates, so `newly_determined_mono` proves inclusion
of the resolved arrows. `direction_count_mono` proves the inequality
for a fixed true DAG. `direction_count_sum_mono` proves it for the
sum with the same candidate class and hence the same denominator.

`one_edge_class_complete` proves that the single-edge example
has exactly the two displayed candidate edge functions.
`one_edge_direction_counts` checks the sum before and after adding the
experiment, which gives means 0 and 1 over the two true DAGs.
`printed_inequality_fails` records the resulting counterexample.

The general proof uses feasible DAGs. Connecting this semantic count
to the paper's Meek algorithm and verifying the union identity in
Lemma 2 and submodularity in Theorem 1 remain separate.

# Lam, Andrews and Ramsey (2022), GRaSP

<!-- topic: Discovery -->

[Paper index](../paper-checks.md)

> **Verified discrepancy** · [Supplement Lemma B.8(c), edge count in the proof](#edge-count-in-lemma-b8c) · The covered reversal preserves the original DAG’s arrow count. Figure 2 shows that the reinduced DAG can be sparser.

*Greedy Relaxations of the Sparsest Permutation Algorithm*, UAI 2022,
PMLR 180, pp. 1052–1062. [Proceedings](https://proceedings.mlr.press/v180/lam22a.html) · [Supplement](https://proceedings.mlr.press/v180/lam22a/lam22a-supp.pdf)

## Tuck and covered reversal

`OrderSplit.tuck` implements Definition 4.1 on the three blocks around the ordered endpoints. It uses the supplied DAG's ancestor predicate to move the middle ancestors of the head ahead of both endpoints. The other middle vertices follow both endpoints. Each block keeps its relative order. `OrderSplit.tuck_perm` proves the result is a permutation of the input, and `OrderSplit.from_order_original` and `OrderSplit.reconstructs_order` connect the executable split to its list decomposition.

`covered_singular` and `singular_all` prove the inclusions between the three edge tiers in Definition 4.2. For a covered edge, `covered_tuck_order` proves that the middle ancestor block is empty. `covered_tuck_is_causal_order` then proves Lemma B.8(a) using the existing Chickering covered reversal on the supplied DAG. [Lean](../../OpenCausalScience/Papers/LamEtAl2022/Tuck.lean)

`covered_tuck_subgraph` proves Lemma B.8(b). Given a CI oracle for which the original DAG is Markov, the DAG reinduced from the tucked order can only use arrows of the covered reversal. The formalization transports the Markov property across the reversal and applies the necessary-arrow property of the order-induced DAG. `covered_tuck_sparsity_and_separations` proves parts (c–d). The reinduced DAG has at most the original arrow count and preserves each d-separation of the original DAG. [Lean](../../OpenCausalScience/Papers/LamEtAl2022/CoveredProjection.lean)

## Bounded search and Figure 2

`Search.first_improvement_sound` and `Search.no_first_improvement_iff` verify the bounded depth-first step of Algorithm 1 on supplied candidates and edge counts. A branch may traverse equal edge counts and must end at a strictly smaller edge count. The search tracks visited DAG keys on the current branch. The depth bound counts moves, including the final improving move. `Search.descend_spec` verifies that the single-tier outer loop of Algorithm 2 terminates at an order with no improvement reachable within that bound. [Lean](../../OpenCausalScience/Papers/LamEtAl2022/Search.lean)

The [oracle search](../../OpenCausalScience/Papers/LamEtAl2022/GRaSP.lean) computes the induced DAG and eligible tucks at every order. `eligible_eq_true_iff` verifies the three tier tests. `search_perm_and_terminal` proves permutation preservation and absence of bounded improvement at the final tier, with each tier initialized by the preceding one.

`Figure2.edge_sets` constructs the three displayed DAGs using the paper's (RU) rule and the Figure 2 independence oracle. `Figure2.covered_tuck_trace` follows the two covered tucks and checks the edge counts against the figure. `Figure2.depth_two_needed` computes the search from the first order. Depth one finds no strict improvement, while depth two returns the displayed two-edge DAG. [Lean](../../OpenCausalScience/Papers/LamEtAl2022/Figure2.lean)

## Edge count in Lemma B.8(c)

The supplement proves the bound using the intermediate covered reversal $H$. The last equality in the proof compares $|E(H)|$ with $|E(G_\tau)|$. The count preserved by reversal is $|E(G_\pi)|$, so the argument is $|E(G_\tau)|\le |E(H)| = |E(G_\pi)|$. `Figure2.edge_count_after_reversal` computes three arrows in the covered reversal of Figure 2(b) and two in the reinduced graph in Figure 2(c). The inequality stated in Lemma B.8(c) follows in general from edge inclusion and the reversal count. [Supplement, p. 4](https://proceedings.mlr.press/v180/lam22a/lam22a-supp.pdf#page=4) · [Proceedings, Figure 2](https://proceedings.mlr.press/v180/lam22a/lam22a.pdf#page=5) · [Lean count proof](../../OpenCausalScience/Papers/LamEtAl2022/EdgeCount.lean)

Theorem 3.5’s derivation of Markovness from a graphoid, the P-minimality reachability theorem (4.5) and the statistical consistency results remain open in Lean.

# Andrews et al. (2023), BOSS and grow–shrink trees

<!-- topic: Discovery -->

Bryan Andrews, Joseph Ramsey, Rubén Sánchez-Romero, Jazmin Camchong and Erich Kummerfeld, *Fast Scalable and Accurate Discovery of DAGs Using the Best Order Score Search and Grow Shrink Trees*, NeurIPS 36, 2023. [Proceedings](https://proceedings.neurips.cc/paper_files/paper/2023/hash/c9cde817d04811ba28e44071bd9f76a5-Abstract-Conference.html) · [Supplement](https://proceedings.neurips.cc/paper_files/paper/2023/file/c9cde817d04811ba28e44071bd9f76a5-Supplemental-Conference.pdf)

## Order search in Algorithms 4–5

`mem_insertions_iff` characterizes every relocation of one vertex as a cut of the fixed list of other vertices. `algorithm_five_eq_best_move` proves that the successive position trials and rollback in Algorithm 5 agree with an incumbent-preserving maximum over those relocations for a duplicate-free order. Both versions accept only strict score increases. `sweep_fixed_at_equal_score` proves that a full sweep with no score gain leaves the order unchanged and rules out improvement by every one-vertex move. `search_perm_and_locally_optimal` proves that repeated full sweeps terminate at such an order and preserve the vertex permutation, for an arbitrary fixed rational order score. [Lean](../../OpenCausalScience/Papers/AndrewsEtAl2023/BestMove.lean)

## Grow–shrink and projection in Sections 2–3

`ranked_improvements_filter` proves that filtering a cached ranking by the eligible prefix gives the same ranking as scoring and sorting only eligible candidates, with label-based tie breaking. `tree_query_eq_grow_shrink` proves that a finite tree caching ranked additions, shrunken parents and scores gives the same parents and score as running grow–shrink again for that prefix. `shrink_properties` proves that each returned parent set is a subset of the input, has at least its input score, and admits no improving deletion. `project` uses the predecessor check to construct a ranked DAG. The reference tree is built eagerly. The score-gain guards make explicit when Algorithms 1–2 stop, as in the authors' implementation. [Lean](../../OpenCausalScience/Papers/AndrewsEtAl2023/GrowShrinkTree.lean) · [Public implementation](https://github.com/bja43/boss/blob/bf937196adac74b7be157b0ae45745ed0efa06ff/gst.py#L13-L35)

`selectedOrder` uses the sum of grow–shrink local scores in the finite search, and `selectedDAG` projects the winning order. Lean checks that the order is locally optimal for that same score and the returned arrows are exactly the selected parents. [Lean](../../OpenCausalScience/Papers/AndrewsEtAl2023/OrderSearch.lean)

## Proposition 2 and search scope

The published large-sample result assumes an i.i.d. sample from a curved exponential family satisfying causal Markov and faithfulness, with backward equivalence search enabled. The proof uses the asymptotic containment of the distribution by the projected DAG and the correctness of backward equivalence search. The formalization proves the finite order search and grow–shrink contracts. General BIC consistency, the distribution-level projection guarantee and MEC recovery with the backward phase remain open here. [Section 4 and Proposition 2](https://proceedings.neurips.cc/paper_files/paper/2023/file/c9cde817d04811ba28e44071bd9f76a5-Paper-Conference.pdf#page=6) · [Chickering (2002), §4.2](https://www.jmlr.org/papers/volume3/chickering02b/chickering02b.pdf#page=17)

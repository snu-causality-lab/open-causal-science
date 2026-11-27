# Richardson (2009), a factorization criterion for acyclic directed mixed graphs

<!-- topic: Graphical Markov models -->

[Paper index](../paper-checks.md)

Thomas S. Richardson, *A Factorization Criterion for Acyclic Directed Mixed
Graphs*, UAI 2009, §§2–4 and Figures 1–2. The reference copy is the original
proceedings PDF reissued in PMLR's UAI archive.
[Proceedings](https://proceedings.mlr.press/r7/richardson09a.html) ·
[Author preprint](https://arxiv.org/abs/1406.6764)

## Lean results

[HeadTail.lean](../../OpenCausalScience/Papers/Richardson2009/HeadTail.lean)
computes the recursive head partition of §3.2. Each round finds the districts
induced by the vertices still present and removes the barren vertices from
each district. Ancestry for barrenness is computed in the full graph.
The code uses the district itself as the input to the barren-set operation.
[HeadCharacterization.lean](../../OpenCausalScience/Papers/Richardson2009/HeadCharacterization.lean)
proves the three statements of Proposition 1 about barrenness, ancestral
closure and passage to subsets.

- `headPartition_cover` and `headPartition_disjoint` prove the coverage and
  disjointness in Corollary 13, including coverage for sets that are not
  ancestral. Directed edges must increase in the given rank.
- `headTail` computes the conditioning set from the district of the head
  in its ancestral closure, as in Definition 5. The reference evaluator
  uses the first member of the head to select that district.
- [Figures.lean](../../OpenCausalScience/Papers/Richardson2009/Figures.lean)
  computes the heads and tails in Figures 1 and 2. In Figure 2 each of the
  two factors conditions on a vertex in the other head. For Figure 1,
  `figure1_all_ancestral_factors` verifies the product of exact rational
  conditional factors for one strictly positive binary distribution over
  all nine ancestral margins and all 16 binary assignments.

The remaining head and tail characterizations and the two probability
implications of Theorem 4 remain open in this formalization.

Source checked against the proceedings PDF, SHA-256
`3b372c944ebcae51e2842c1e5ddef22daeaf06cf106709e4931d4a86670ddece`.

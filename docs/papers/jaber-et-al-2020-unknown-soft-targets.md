# Jaber, Kocaoglu, Shanmugam and Bareinboim (2020), soft interventions with unknown targets

<!-- topic: Discovery -->

A candidate consists of a causal DAG with latent variables and an
ordered tuple of proposed intervention regimes. Each targeted variable
has a mechanism label. When two regimes both target a variable but
assign different mechanisms, that variable enters the difference used
in the augmentation. [Definitions 1–4](https://proceedings.neurips.cc/paper/2020/file/6cd9313ed34ef58bad3fdd504355e72c-Paper.pdf#page=4)

## Mechanism comparisons

[PsiAugmentation.lean](../../OpenCausalScience/Papers/JaberEtAl2020/PsiAugmentation.lean)
proves that the comparison list retains every pair of distinct regime
positions in tuple order. Each pair has its own F-node. `psi_root_edge_iff`
characterizes its children by inequality of the two mechanism entries.
Mechanism labels are compared within each variable. An absent entry
represents its original mechanism. Proposition 1, the paper’s
Equation (2), follows from the
[general ordinary d-separation result](kocaoglu-et-al-2019-controlled-soft-interventions.md#augmentation-and-ordinary-d-separation)
for graphs with added roots.

## Figure 1 and Example 3

[Figure1.lean](../../OpenCausalScience/Papers/JaberEtAl2020/Figure1.lean)
checks all 160 pairwise visible d-separation answers for the first two
candidate pairs in the figure. The augmented DAGs have different direct
`F₁ → W` statuses and the same visible d-separation answers. Both make
`F₁` and `W` inseparable by any subset of the other observed variables.
The third pair separates them unconditionally. Example 3 checks the
addition of `F₁ → Z` when the two regimes change `Z` to different
mechanisms, along with the ordinary and cross-regime separation queries
shown in the paper. [Figure 1 and Examples 3–5](https://proceedings.neurips.cc/paper/2020/file/6cd9313ed34ef58bad3fdd504355e72c-Paper.pdf#page=5)

The [public CGA routine](https://github.com/snu-causality-lab/cga/blob/main/docs/reference/SOFT_INTERVENTION.md)
marginalizes the latent vertices of each augmented DAG and compares the
resulting MAGs. The general cross-regime d-separation equivalence in
Equation (3), the probability interpretation of Ψ-Markov equivalence,
and Ψ-FCI's soundness and completeness remain open in Lean.

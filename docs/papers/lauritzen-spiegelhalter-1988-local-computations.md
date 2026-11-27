# Lauritzen and Spiegelhalter (1988), local probability computations

<!-- topic: Graphical Markov models -->

The paper computes probabilities locally by converting a network into
a representation with clique potentials and separator updates.
[JRSS B 50, pp. 157–194](https://doi.org/10.1111/j.2517-6161.1988.tb01721.x)

[TreeMessages.lean](../../OpenCausalScience/Papers/LauritzenSpiegelhalter1988/TreeMessages.lean)
implements the finite, division-free upward message for a rooted bag
tree. The two mutually recursive programs compute messages and
enumerate compatible bag assignments with their weights.
`upward_message_exact` proves their equality for arbitrary finite bag
tables and separator checks. In the chain `A — B — C`, with two
copy probabilities of `3/4`, both calculations give the joint
evidence mass `P(A=1,C=1)=5/16`.

[SeparatorGluing.lean](../../OpenCausalScience/Papers/LauritzenSpiegelhalter1988/SeparatorGluing.lean)
proves that the normalized product of two finite clique marginals
recovers both when they share the same separator marginal. If the
separator cell has zero mass, nonnegativity forces every attached
cell to have zero mass, and the joined cell is zero.

The tree message theorem assumes a given bag tree. Running
intersection is supported by the [elimination-bag construction](lauritzen-speed-vijayan-1984-decomposable-graphs.md).
Refining the paper's absorption updates and both propagation passes,
and combining graph construction with the full probability algorithm,
are separate obligations.

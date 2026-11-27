# Lauritzen and Sadeghi (2018), unifying Markov properties for graphical models

<!-- topic: Graphical Markov models -->

[Paper index](../paper-checks.md)

Steffen Lauritzen and Kayvan Sadeghi, *Unifying Markov Properties for Graphical
Models*, Annals of Statistics 46(5), 2251–2278, §3.2 and Lemma 2.
[Journal article](https://doi.org/10.1214/17-AOS1618) ·
[Author preprint, v4](https://arxiv.org/abs/1608.05810v4)

## Lean results

[ConnectingWalks.lean](../../OpenCausalScience/Papers/LauritzenSadeghi2018/ConnectingWalks.lean)
proves the connecting-walk equivalence in Lemma 2 for the supported marked
mixed graphs. An arrowhead cannot meet a line endpoint, so a collider
section consists of a single vertex. The section walk requires that vertex
to be in the conditioning set. An m-connecting walk can use an ancestor of
the conditioning set instead. In the proof, a directed detour follows the
ancestor to a conditioned descendant and returns before continuing along
the original walk. The reverse implication uses reflexive ancestry.
The equivalence assumes that both endpoint sets avoid the conditioning set.

The general four-edge-type representation and the unification of all its
graph subclasses in Theorem 2 remain open. The separate LWF, AMP and
multivariate regression records give their own scopes.

Source checked against arXiv:1608.05810v4, PDF SHA-256
`a0d8d18810b5bf45c0fa3f16988413da63dd344eb207f4fd2d7d9155245d27fd`.

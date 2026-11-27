# Sadeghi and Lauritzen (2014), Markov properties for mixed graphs

<!-- topic: Graphical Markov models -->

[Paper index](../paper-checks.md)

Kayvan Sadeghi and Steffen L. Lauritzen, *Markov Properties for Mixed
Graphs*, Bernoulli 20(2), 676–696. The Lean results use Theorem 1 in §3
and the canonical conditioning set from Lemma 6 and §6.1.
[Journal article](https://doi.org/10.3150/12-BEJ502) ·
[Published PDF](https://discovery.ucl.ac.uk/id/eprint/10068613/1/Sadeghi_euclid.bj.1393594002.pdf)

## Lean results

[Markov.lean](../../OpenCausalScience/Papers/SadeghiLauritzen2014/Markov.lean)
proves symmetry, decomposition, weak union, contraction, intersection and
composition for the independence relation induced by m-separation on the
finite graphs supported by `MixedGraph`. These include ADMGs and ancestral
graphs. Weak union follows an active walk up to a newly activated collider
and continues to a descendant in the added conditioning set. Contraction
and intersection stop the walk at its first vertex in either target set.

`canonical_pairwise_separator` proves that if any legal conditioning set
separates a pair of endpoint sets, the endpoint anterior set with the
endpoints removed also separates. Specializing to two vertices gives
`pairwise_of_global` under maximality stated as the existence of a separator
for each nonadjacent pair. These two results use the existing reduction to
the undirected collider augmentation.

The paper's Theorem 1 allows all loopless mixed graphs. The Lean
`MixedGraph` type restricts arrowheads at endpoints of undirected edges.
The full ribbonless anterior transformation and the pairwise-to-global
implication of Theorem 3 remain open.

Source checked against the published PDF, SHA-256
`a7cda56df9c5ca07c13a001516d4d6f49bc4805b9b2b6577fa3cf276d289bc81`.

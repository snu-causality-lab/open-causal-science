# Lauritzen, Speed and Vijayan (1984), decomposable graphs and hypergraphs

<!-- topic: Graphical Markov models -->

The paper characterizes decomposability of a graph's clique hypergraph
by triangulation. Its perfect ordering of cliques gives the running
intersection used for compatibility of probability marginals.
[Journal of the Australian Mathematical Society 36, Theorem 2](https://doi.org/10.1017/S1446788700027300)

[EliminationBags.lean](../../OpenCausalScience/Papers/LauritzenSpeedVijayan1984/EliminationBags.lean)
starts with a supplied perfect elimination order. The later
neighbours of a vertex form a clique. The bag of the vertex is that
clique together with the vertex. Every nonterminal bag attaches to
its earliest later neighbour's bag and its later neighbours are all
present in the parent bag.

`running_intersection` constructs a parent path from every bag
containing a vertex to that vertex's own bag, staying in the bags
that contain it. This proves running intersection for elimination
bags, which can include nonmaximal cliques. Constructing a perfect
elimination order from an arbitrary chordal graph, restricting the
forest to maximal cliques, and the reverse implication of Theorem 2
are separate. [Probability messages](lauritzen-spiegelhalter-1988-local-computations.md)

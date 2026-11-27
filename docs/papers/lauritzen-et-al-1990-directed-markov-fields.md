# Lauritzen, Dawid, Larsen and Leimer (1990), directed Markov fields

<!-- topic: Graphical Markov models -->

The paper relates directed local and global Markov properties, and
recursive factorization for laws dominated by a product measure. Its
finite DAG argument does not require a strictly positive density.
[Networks 20, pp. 491–505](https://doi.org/10.1002/net.3230200503)

## Ordered local property and factorization

[OrderedFactorization.lean](../../OpenCausalScience/Papers/LauritzenEtAl1990/OrderedFactorization.lean)
uses a topological labelling of the vertices and the
[shared finite conditional-independence definition](../../OpenCausalScience/Probability/ConditionalIndependence.lean).
`ordered_local_factorization` turns the ordered local parent-cell CI
into the full observational mass product. At unsupported parent cells,
zero prefix masses follow from event inclusion. Any supplied
default state gives a valid conditional factor on those cells, with
no effect on the observational product.

## From graph separation to probability

[KernelElimination.lean](../../OpenCausalScience/Papers/LauritzenEtAl1990/KernelElimination.lean)
proves that summing normalized sink factors along a checked elimination
order leaves the retained ancestral product. The shared
[ancestral moralization](../../OpenCausalScience/Graph/Moralization.lean)
turns d-separation into graph separation.
[MoralFactorization.lean](../../OpenCausalScience/Papers/LauritzenEtAl1990/MoralFactorization.lean)
proves that each unconditioned child-parent family belongs to one
component side of the moral separation and splits the retained
density on that partition. Its `ordered_local_separation` also proves
the graphical query needed for reading the ordered local property from
the global one.

[ProductLaw.lean](../../OpenCausalScience/Probability/ProductLaw.lean)
proves independence of side observables on a split finite product.
`moral_product_law` assembles the graph and probability arguments
for a supplied Cartesian enumeration of the fixed-condition slice.
`splice_eq_iff` proves uniqueness of its component assignments when
unused coordinates are fixed. Relating this enumeration and the
elimination order to an arbitrary supplied joint law is a separate
obligation. The measure-theoretic version is outside the finite model.

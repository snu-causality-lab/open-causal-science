# Sullivant, Talaska and Draisma (2010), trek separation

<!-- topic: Linear graphical models -->

[Definition 2.7](https://pure.tue.nl/ws/portalfiles/portal/3002904/Metis230934.pdf#page=6) · [Proposition 3.5](https://pure.tue.nl/ws/portalfiles/portal/3002904/Metis230934.pdf#page=14)

The [Lean companion](../../OpenCausalScience/Papers/SullivantEtAl2010/TrekSeparation.lean)
relates the two sides of a trek in a finite DAG to a path in the paper's
two-copy graph. Arrows are reversed on the left, unchanged on the right, and
a route crosses once from a left vertex to its right copy. Left and right
vertices are blocked independently.

`route_iff_unblocked_trek` proves that a surviving left-to-right route is
equivalent to a pair of unblocked paths with a common top. Consequently
`separates_iff_no_route` reduces the trek separation test to ordinary
reachability in the two-copy graph. `overlap_requires_removal` checks the
zero-length trek boundary when a vertex belongs to both endpoint sets.

The minimum-cut size and the covariance rank characterization in Theorem 2.8
remain open here. The [single-factor tetrad companion](silva-et-al-2006-linear-latent-structure.md)
checks the covariance equality directly in a simple measurement model.

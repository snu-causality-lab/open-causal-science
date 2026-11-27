# Grimmett (1973), random fields

<!-- topic: Graphical Markov models -->

Geoffrey Grimmett, *A Theorem about Random Fields*, Bulletin of the London Mathematical Society **5**(1), 81–84. The theorem on pp. 82–84 constructs Gibbs potentials for a positive Markov field by Möbius inversion. [Version of record](https://doi.org/10.1112/blms/5.1.81) · [Author's copy](https://www.statslab.cam.ac.uk/~grg1000/papers/blms5-81.pdf)

- [CliqueFactorization.lean](../../OpenCausalScience/Papers/Grimmett1973/CliqueFactorization.lean) takes a duplicate-free listing of graph vertices, an anchor assignment, and a positive rational table. `multiplicative_mobius_inversion` factors the table into anchored interactions. Under the pairwise Markov property, `interaction_one_of_nonedge` shows that an interaction is one when its scope contains a nonadjacent pair.
- `pairwise_markov_iff_clique_factorization` proves that all conditional 2×2 determinants at nonedges vanish exactly when the table factors over cliques. The potential factors are constructed by ratios. The state type may vary by vertex, and the algebra allows unnormalized tables. `clique_factors_imply_pairwise_markov` also holds for tables with zeros.

The pairwise property uses determinants at fixed configurations of the other vertices. Analytic Gibbs energies and the separate equivalence to a global graphical separation property are outside this module. [Lean toolchain](../../lean-toolchain) · [Four-cycle example at zero cells](moussouris-1974-gibbs-markov-constraints.md)

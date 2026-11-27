# Besag (1974), spatial interaction

<!-- topic: Graphical Markov models -->

Julian Besag, *Spatial Interaction and the Statistical Analysis of Lattice Systems*, Journal of the Royal Statistical Society Series B **36**(2), 192–225, followed by discussion. Sections 2–3 derive neighborhood models and the Hammersley–Clifford representation under positivity. [Version of record](https://doi.org/10.1111/j.2517-6161.1974.tb00999.x) · [Article and discussion](https://www2.stat.duke.edu/~scs/Courses/Stat376/Papers/GibbsFieldEst/BesagJRSSB1974.pdf)

[The shared clique factorization formalization](../../OpenCausalScience/Papers/Grimmett1973/CliqueFactorization.lean) gives the positive rational counterpart on a finite graph. Anchor values play the role of reference states. `positive_clique_factorization` constructs positive clique-local factors from the cross-product conditions for pairs of nonneighbors. `clique_factors_imply_pairwise_markov` proves the reverse implication. The proof uses multiplicative interactions instead of the additive potentials obtained by taking logarithms. [Grimmett companion](grimmett-1973-random-fields.md)

The checked result concerns the representation of the joint table. Besag's spatial examples and estimation methods have a different scope. [Lean toolchain](../../lean-toolchain)

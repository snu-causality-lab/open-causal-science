# Moussouris (1974), Gibbs and Markov fields with constraints

<!-- topic: Graphical Markov models -->

John Moussouris, *Gibbs and Markov Random Systems with Constraints*, Journal of Statistical Physics **10**(1), 11–33. Figure 3(a), p. 22, shows a binary four-cycle whose zero cells obstruct Gibbs factorization. Geiger, Meek and Sturmfels list its eight equiprobable configurations in Example 7, Eq. (4.12). [Version of record](https://doi.org/10.1007/BF01011714) · [Article scan](https://www.academia.edu/52068823/Gibbs_and_Markov_random_systems_with_constraints) · [Published reconstruction](https://math.berkeley.edu/~bernd/AOS0092.pdf#page=18)

- [FourCycle.lean](../../OpenCausalScience/Papers/Moussouris1974/FourCycle.lean) checks normalization and the pairwise Markov condition. The latter checks the determinants for both opposite pairs in every fixed stratum. `every_clique_projection_is_realized` shows that each clique projection of the absent configuration `0010` occurs in a supported configuration.
- `pairwise_markov_not_clique_factorization` combines the checked determinants with the support argument. A finite clique factor can depend only on its own scope, so the projected supported configuration forces that factor to be nonzero at `0010`. The product is then nonzero, contradicting the zero joint probability.

This example makes the direction that needs positivity in the [Markov-to-clique-factorization theorem](grimmett-1973-random-fields.md) concrete. The Lean statements use pairwise determinants and arbitrary clique-local rational factors. [Lean toolchain](../../lean-toolchain)

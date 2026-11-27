# Darroch, Lauritzen and Speed (1980), graphical log-linear models

<!-- topic: Graphical Markov models -->

John Darroch, Steffen Lauritzen and Terry Speed, *Markov Fields and Log-Linear Interaction Models for Contingency Tables*, Annals of Statistics **8**(3), 522–539. Sections 2–3 relate the nearest-neighbor Gibbs representation to graphical models for contingency tables. [Version of record](https://doi.org/10.1214/aos/1176345006) · [Authors' 1978 preprint](https://www.math.ku.dk/bibliotek/arkivet/preprints-fra-ims/1978/Preprint_1978_-_No_11_Darroch__JN__Lauritzen__SL__Speed__TP_-_Markov_Fields_and_Log-Linear_Interaction_Models---.pdf)

[The shared clique factorization formalization](../../OpenCausalScience/Papers/Grimmett1973/CliqueFactorization.lean) proves `pairwise_markov_iff_unit_nonclique_interactions`. A positive rational table satisfies the pairwise Markov property exactly when all anchored interactions indexed by noncliques are one. This is the multiplicative form of the zero restrictions on nonclique log-linear interactions. The reverse direction reconstructs the table from the clique interactions.

This proof concerns the positive-table representation. The paper also studies decomposability, dimensions, and estimation. [Grimmett companion](grimmett-1973-random-fields.md) · [Lean toolchain](../../lean-toolchain)

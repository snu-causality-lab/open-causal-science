# Tian and Pearl (2003), generalized Q-decomposition

<!-- topic: Identification -->

[Paper index](../paper-checks.md)

Lemma 4(ii) in *On the Identification of Causal Effects* obtains a
c-factor by taking the ratios of consecutive prefix marginals at the
positions occupied by that c-component in a topological order. Equation
(71) gives the ratios. Equation (72) obtains the prefix marginals from
the input kernel. [Technical report R-290-L, Lemma 4](https://ftp.cs.ucla.edu/pub/stat_ser/R290-L.pdf#page=22)

[QDecomposition.lean](../../OpenCausalScience/Papers/TianPearl2003/QDecomposition.lean)
checks the ratio calculation for finite rational prefix masses. The
premises require distinct block labels, a product of partial block factors
at every prefix, and a change only to the block containing the new vertex.
For a prefix with nonzero mass,
`prefix_ratio_eq_block_ratio` cancels the unchanged factors.
`recovered_factor_eq_final` proves that multiplying the selected ratios
recovers the final factor from its empty-prefix value of one. The
graphical derivation of the prefix factorization and marginalization
premises in Lemmas 3–4 is separate.

Figure 7 uses this construction in the recursive step of `Identify`.
[IdentifyRecurrence.lean](../../OpenCausalScience/Papers/TianPearl2003/IdentifyRecurrence.lean)
implements the graph plan. The routine first marginalizes to the target's
ancestors and then extracts the c-factor containing the target.
`recursive_set_smaller` proves that each recursive call strictly decreases
the number of retained vertices.
`ancestors_eq_current_of_no_decrease` proves that a step with no decrease
has reached the full current ancestor set. Figure 7's fixed-point branch
reports failure to determine `Q[C]`. This Lean module checks the graph
steps. Evaluation of the planned kernel expressions and the interpretation
of failure require separate results. [Figure 7 and following discussion](https://ftp.cs.ucla.edu/pub/stat_ser/R290-L.pdf#page=26)

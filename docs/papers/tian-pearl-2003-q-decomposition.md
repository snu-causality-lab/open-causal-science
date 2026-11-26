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

## Ancestral marginalization and the product of c-factors

[AncestralMarginal.lean](../../OpenCausalScience/Papers/TianPearl2003/AncestralMarginal.lean)
proves Lemma 3's intervention and marginalization identity for ranked
binary structural models with a finite rational exogenous law. An
unclamped parent of a retained vertex must be retained. Fixing the other
unclamped vertices then preserves the retained responses on every unit.
`ancestral_marginal_equals_kernel` sums the old kernel cells on the
removed coordinates and returns the new kernel's retained event mass.
Latent roots may remain in the graph while the event reads only the
retained observed responses.

[DistrictProduct.lean](../../OpenCausalScience/Papers/TianPearl2003/DistrictProduct.lean)
proves the probability calculation in Lemma 4(i).
`joint_mass_eq_product_factors` sums the product likelihood over a
Cartesian list of primitive root assignments and yields the product of
the separately marginalized factors. The premise assigns each
component its own independent block and a block-local likelihood at the
fixed observed and intervention cell.

## The Identify recursion

Figure 7 uses this construction in the recursive step of `Identify`.
[IdentifyRecurrence.lean](../../OpenCausalScience/Papers/TianPearl2003/IdentifyRecurrence.lean)
implements the graph plan. [IdentifyReachability.lean](../../OpenCausalScience/Papers/TianPearl2003/IdentifyReachability.lean)
proves that its ancestry and c-component tests agree with finite
reachability in the current induced graph. The routine first marginalizes
to the target's ancestors and then extracts the c-factor containing the target.
`recursive_set_smaller` proves that each recursive call strictly decreases
the number of retained vertices.
`ancestors_eq_current_of_no_decrease` proves that a step with no decrease
has reached the full current ancestor set.

[IdentifyCorrectness.lean](../../OpenCausalScience/Papers/TianPearl2003/IdentifyCorrectness.lean)
executes the plan using kernel operations.
`successful_plan_returns_target` proves that every successful execution
returns `Q[C]` when the two local kernel operations obey the stated
marginalization and extraction laws. Figure 7's fixed-point branch
produces no kernel. Proving nonidentifiability from that branch takes a
separate completeness argument. [Figure 7 and following discussion](https://ftp.cs.ucla.edu/pub/stat_ser/R290-L.pdf#page=26)

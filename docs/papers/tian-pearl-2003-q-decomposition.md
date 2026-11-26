# Tian and Pearl (2003), generalized Q-decomposition

<!-- topic: Identification -->

[Paper index](../paper-checks.md)

In *On the Identification of Causal Effects*, Lemma 3 gives ancestral
marginalization of a causal factor. Lemma 4(i) factors a kernel over its
c-components. Lemma 4(ii) recovers each component by multiplying the
ratios of consecutive prefix marginals at its positions in a topological
order. [Technical report R-290-L, Eqs. (69)–(72)](https://ftp.cs.ucla.edu/pub/stat_ser/R290-L.pdf#page=21)

The [finite-SCM proof](../../analysis/OpenCausalScienceAnalysis/Identification/QFactor.lean)
uses finite variable spaces and independent finite exogenous roots. Each
root can occur in any number of structural equations, and the causal
diagram records the pairs that share a root. The report's semi-Markovian
model gives each latent root exactly two observed children.
`Q_marg_ancestral` and
`Q_prod_ccomps` prove the marginalization and product identities.
`cfac_eq_Q` proves the recovery formula when its selected denominators
are positive, and `Q_pos_of_observational_pos` obtains causal-factor
positivity from positive observational mass at the same assignment.

## Ancestral marginalization and the product of c-factors

[AncestralMarginal.lean](../../OpenCausalScience/Papers/TianPearl2003/AncestralMarginal.lean)
proves Lemma 3's intervention and marginalization identity for ranked
binary structural models with a finite rational exogenous law. An
unclamped parent of a retained vertex must be retained. Fixing the other
unclamped vertices then preserves the retained responses on every unit.
`ancestral_marginal_equals_kernel` sums the old kernel cells on the
removed coordinates and returns the new kernel's retained event mass.
Latent roots may remain in the graph while the event reads only the
retained observed responses. The event-mass and partition identities
are in [FiniteMass.lean](../../OpenCausalScience/Probability/FiniteMass.lean).

[DistrictProduct.lean](../../OpenCausalScience/Papers/TianPearl2003/DistrictProduct.lean)
proves the probability calculation in Lemma 4(i).
`joint_mass_eq_product_factors` sums the product likelihood over a
Cartesian list of primitive root assignments and yields the product of
the separately marginalized factors. The premise assigns each
component its own independent block and a block-local likelihood at the
fixed observed and intervention cell.

[QDecomposition.lean](../../OpenCausalScience/Papers/TianPearl2003/QDecomposition.lean)
isolates the finite rational ratio calculation. Given distinct block labels,
prefix products, and a change only to the block containing the new vertex,
`prefix_ratio_eq_block_ratio` cancels the unchanged factors at a nonzero
prefix. `recovered_factor_eq_final` shows that the selected ratios telescope
to the final factor.

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

[IdentifyFixing.lean](../../OpenCausalScience/Papers/TianPearl2003/IdentifyFixing.lean)
connects the first graph step to fixing. Given a topological ranking of
the directed edges, `fixing_order_to_ancestors` finds a valid graphical
fixing order that removes exactly the nonancestors. Each step fixes a
highest-ranked remaining nonancestor, whose directed descendants all
remain nonancestors. The district-extraction step and the effect of
fixing on a probability kernel require separate results.

[IdentifyCorrectness.lean](../../OpenCausalScience/Papers/TianPearl2003/IdentifyCorrectness.lean)
executes the plan using kernel operations.
`successful_plan_returns_target` proves that every successful execution
returns `Q[C]` when the two local kernel operations obey the stated
marginalization and extraction laws. The [finite-SCM instance](../../analysis/OpenCausalScienceAnalysis/Identification/TianKernelOperations.lean)
supplies these laws from Lemmas 3 and 4 and uses the causal diagram of
the SCM as the input graph. When every full assignment has positive observational mass,
`successful_identify_eq_Q` proves that running the plan on the supplied
causal factor and returning a kernel yields the target factor.
Figure 7's fixed-point branch returns no kernel. [Figure 7](https://ftp.cs.ucla.edu/pub/stat_ser/R290-L.pdf#page=26)

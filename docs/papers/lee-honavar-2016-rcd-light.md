# Lee and Honavar (2016), RCD-Light

<!-- topic: Discovery -->

> **Verified discrepancy** · [Appendix, maximal pivots and the proof of Lemma 5](#the-appendix-corrections) · The maximal-pivot set uses the forward word twice, and the unequal-pivot formula uses a one-sided difference.

Sanghack Lee and Vasant Honavar, *On Learning Causal Models from Relational Data*, AAAI 2016, pp. 3263–3270. The Lean development uses the appendix corrections dated 2026-11-27. The correction is unofficial and author review is pending. [Proceedings](https://doi.org/10.1609/aaai.v30i1.10417) · [Correction PDF](https://www.sanghacklee.me/ai-corrected/RCDLight_AI_corrected_2026-11-27.pdf)

## The appendix corrections

The maximal-pivot bound uses `pivots(Q,Q)` where the appendix used `pivots(reverse Q,Q)`. In the proof of Lemma 5, the unequal-pivot index is `|Q| − m + 1 + max(0,n − m)`. [RCDLight.lean](../../OpenCausalScience/Papers/LeeHonavar2016RCDLight/RCDLight.lean) gives counterexamples to the printed expressions and checks the corrected indices.

[RCDPathValidity.lean](../../OpenCausalScience/Papers/LeeHonavar2016RCDLight/RCDPathValidity.lean) proves the corrected Lemma 5 in `RCDPathValidity.representative_unshielded_triple`. The result preserves the two inducing dependencies and constructs a representative with nonintersectable flanks. Terminal sets use whole-history bridge burning on finite legal skeletons. The proof handles equal and unequal pivots, including repeated endpoint attributes. [BridgeBurningEnumeration.lean](../../OpenCausalScience/Papers/LeeHonavar2016RCDLight/BridgeBurningEnumeration.lean) connects the construction to Algorithm 1's finite enumeration.

## Algorithm 1

[Algorithm1.lean](../../OpenCausalScience/Papers/LeeHonavar2016RCDLight/Algorithm1.lean) proves Theorem 1 in `RCDLight.Learning.algorithm1_sound`. For acyclic, well-typed dependencies within the supplied hop bound, the learner recovers the exact undirected dependency pairs, retains all true directions among its alternatives, and every direction it asserts is sound. The theorem assumes an exact ground d-separation oracle and sound background information. It proves closure under the four class orientation rules and treats the inference at line 19 as strict class ancestry.

[FullAdjacency.lean](../../OpenCausalScience/Papers/LeeHonavar2016RCDLight/FullAdjacency.lean) proves the well-typed case of Lemma 1. [GroundOracle.lean](../../OpenCausalScience/Papers/LeeHonavar2016RCDLight/GroundOracle.lean) proves the canonical parent separator used by the learner. [OrientationWitness.lean](../../OpenCausalScience/Papers/LeeHonavar2016RCDLight/OrientationWitness.lean) proves the representative case of Lemma 2 used in Algorithm 1. These files cover oracle soundness and closure. Noncanonical instances of Lemma 2, maximal orientation, comparison with RCD, and empirical performance are outside the verified scope.

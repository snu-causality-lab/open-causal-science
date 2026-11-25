# Ali, Richardson and Spirtes (2009), MAG equivalence

<!-- topic: Graph equivalence -->
<!-- index-anchor: ali-richardson-and-spirtes-2009-mag-equivalence -->

[Paper index](../paper-checks.md)

[Proposition 3.6 and Figures 4 and 6](https://doi.org/10.1214/08-AOS626) separate adjacency and unshielded-collider agreement from the additional constraints in Theorem 3.7. Lean proves Proposition 3.6 when each nonadjacent pair has a separating set. In Figure 4, the first two graphs have identical separation signatures. The first and third share adjacencies and unshielded colliders, while their answers differ for one conditioning query. Both panels in Figure 6 verify equivalence by inspecting all legal singleton queries, and the displayed vertex sequence has different discriminating-path status between members. The general colliders-with-order algorithm remains a separate proof obligation. [Necessary conditions](../../OpenCausalScience/Papers/AliRichardsonSpirtes2009/EquivalenceNecessary.lean) · [Figures 4 and 6](../../OpenCausalScience/Papers/AliRichardsonSpirtes2009/Figures4And6.lean)

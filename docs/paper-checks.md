# Paper checks

For the complete list of author-hosted homepage corrections and the Lean scope of each, see the [homepage correction reviews](errata.md).

## Lee and Bareinboim (2018), structural causal bandits

*Structural Causal Bandits: Where to Intervene?*, NeurIPS 2018. The paper repository contains both the Python implementation and a Lean package for MIS and POMIS, including the Lean version of the POMIS enumeration algorithm and its correctness theorem (`Mec.Scb2018.thm9`). The formalization records its assumptions and follows the statement numbers in the author-hosted, unofficial proof update of 2026-11-23. [Proceedings](https://papers.neurips.cc/paper_files/paper/2018/hash/c0a271bc0ecb776a094786474322cb82-Abstract.html) · [Lean scope and build](https://github.com/sanghack81/SCMMAB-NIPS2018/blob/49b6c9f/lean/README.md) · [Python code](https://github.com/sanghack81/SCMMAB-NIPS2018/tree/49b6c9f/npsem)

On the six-vertex graph from Figure 2, the Python implementation at `49b6c9f` returns the interventional border `{S, T}`, the POMISs `{{S, T}, {T, W}, {T, W, X}}`, and 18 MISs. These agree with the Lean results for that input. [Python enumerators](https://github.com/sanghack81/SCMMAB-NIPS2018/blob/49b6c9f/npsem/where_do.py) · [Lean Figure 2](https://github.com/sanghack81/SCMMAB-NIPS2018/blob/49b6c9f/lean/MecLean/Scb2018/Fig2.lean)

Run this example from the root of the paper repository at that revision.

```python
from npsem.model import CausalDiagram
from npsem.where_do import MISs, MUCT_IB, POMISs

graph = CausalDiagram(
    "STWXYZ",
    [("S", "W"), ("W", "Y"), ("T", "X"), ("T", "Y"), ("Z", "X"), ("X", "Y")],
    [("W", "X", "u_WX"), ("Z", "Y", "u_ZY")],
)
assert MUCT_IB(graph, "Y") == (frozenset("WXYZ"), frozenset("ST"))
assert POMISs(graph, "Y") == {frozenset("ST"), frozenset("TW"), frozenset("TWX")}
assert len(MISs(graph, "Y")) == 18
```

## Lee, Correa and Bareinboim (2019), gID erratum

The July 2022 R-46e adds positivity of the supplied distributions to Definition 4 and updates the upper and bottom equations. Lean evaluates the upper model directly with (A.2) and checks the frontier toggle and biased root noise. The [erratum review](errata-reviews/graphs-and-identification.md#lee-correa-and-bareinboim-2019) describes the checked assumptions for supplied-law positivity and agreement, and for target root parity. [UAI 2019 paper](https://proceedings.mlr.press/v115/lee20b.html) · [July 2022 erratum](https://causalai.net/r46e.pdf)

## Jung, Park and Lee (2024), sequential adjustment correction

The proceedings' Definition 7 and the October 25, 2026 revision use different graphs for forbidden descendants. In the corrected Section 4 example `X₁ → Z → X₂ → Y`, block `{Z}` is admissible at stage 1. The published condition forbids `Z`. Removing incoming arrows into `X₂` leaves the corrected first-stage forbidden set empty. The corrected PDF has SHA-256 `e5f0a7a415aeff87f56bb4482cdbfe33800f3efd3e15a30649ac5c7980ae737c`. [Proceedings](https://proceedings.neurips.cc/paper_files/paper/2024/hash/233ff375b9795cd890f78a1f64459b8d-Abstract-Conference.html) · [Corrected version, pp. 7 and 10](https://www.sanghacklee.me/ai-corrected/SAC_AI_corrected_2026-10-25.pdf)

[SequentialAdjustment.lean](../OpenCausalScience/Papers/JungEtAl2024/SequentialAdjustment.lean) checks rejection by the published rule and acceptance at both stages of the corrected rule. It proves the example's adjustment identity for normalized rational kernels under the chain factorization and checks both pruning examples in Section 4.1. The general graph lemma shows a forbidden descendant in the intervened DAG is still forbidden in the original DAG for a singleton treatment and outcome. The general finite rational formula now follows from the sequential stage equations, which are derived from exchangeability and consistency under the stated alignment and support conditions. Graphical sufficiency, necessity and finder correctness remain open here. [Sequential formula](../OpenCausalScience/Papers/JungEtAl2024/SequentialFormula.lean)

The public [minSAC implementation at `a6d726e`](https://github.com/snu-causality-lab/minSAC/tree/a6d726e274e1ede25666f9655fff927722f6582d) accepts `({Z}, ∅)` on the Section 4 chain. On the second four-node example, it rejects `(∅, ∅)` and constructs `(∅, {C})`. These are replays of the two finite inputs in the corrected paper.

## Kim, Hwang and Lee (2024), DEDUCE-DEP correction

The September 20, 2026 revision starts PC at conditioning-set size zero in Algorithm 3. Its Appendix D counts repeated recursive call occurrences in the all-independent case even when individual CI answers are cached. The corrected PDF has SHA-256 `bce54960fd555465693f078351dcc64a45637449b5d97a964a50ee06b74665cc`. [Proceedings](https://proceedings.mlr.press/v244/kim24a.html) · [Corrected version, pp. 6 and 19](https://www.sanghacklee.me/ai-corrected/deduce_dep_AI_corrected_2026-09-20.pdf)

[DeduceDep.lean](../OpenCausalScience/Papers/KimEtAl2024/DeduceDep.lean) checks the missed edge deletion on the two-vertex empty DAG, derives the lower-order dependence rule from explicit CI axioms, and proves the `3m` branching recurrence above a fixed cutoff. For the all-independent tree without recursion-result memoization, the call count exceeds any fixed multiplier times a fixed natural base to the depth. The recurrence concerns the call tree, and the edge example concerns only the marginal deletion step. [Paper's software repository](https://github.com/snu-causality-lab/deduce-dep/tree/29393a10dde7b0bbe8f32d449c3e735f939321fa)

The public Python routine skips recursion when the same separating set is already recorded. On an empty four-vertex DAG with a size-two conditioning set and cutoff zero, it makes 16 calls including the initial call. The uncached recurrence gives 25 calls for that input. The replay counted entries to `deduce_dep` with exact independence answers. [Pinned Python routine](https://github.com/snu-causality-lab/deduce-dep/blob/29393a10dde7b0bbe8f32d449c3e735f939321fa/src/cddd/deductive_reasoning.py#L25)

## Finite DAG and ancestral graph separation

[Shachter (1998)](https://web.stanford.edu/~shachter/pubs/bayesbl.pdf) gives the directional Bayes-ball search. The [Lean DAG worklist](../OpenCausalScience/Papers/KimEtAl2026/BayesBallCorrectness.lean) proves reachability is equivalent to connection by a vertex-simple active path with the stated endpoint conventions.

[Richardson and Spirtes (2002)](https://doi.org/10.1214/aos/1031689015), §3.4 and Figure 9, use endpoint marks to classify colliders. [MSeparation.lean](../OpenCausalScience/Graph/MSeparation.lean) proves the reference evaluator returns true exactly when a simple m-connecting path exists in a finite graph with at most one marked edge per pair. In [Figure 9](../OpenCausalScience/Papers/RichardsonSpirtes2002/Figure9.lean), the missing adjacency in (a) has no separator among the four legal conditioning sets, and the complete extension in (b) has the same separation answers for every singleton pair and legal conditioning set. The [authors' errata](https://sites.stat.washington.edu/tsr/website/documents/2002/annals-2002-errata.txt) address other locations. The CGA state-based search, graphs with bows, and the general augmentation theorem require separate correspondence proofs.

## Verma and Pearl (1990), DAG equivalence

[Lemmas 1–2 and Theorem 1](https://arxiv.org/pdf/1304.1108) characterize labelled DAG equivalence using the skeleton and unshielded colliders. [DAGEquivalence.lean](../OpenCausalScience/Papers/VermaPearl1990/DAGEquivalence.lean) proves the necessary direction for equality of finite DAG d-separation answers. An arrow admits no separating query for its endpoints. Two nonadjacent vertices have a separating set drawn from the parents of one endpoint. In an unshielded triple, a separating set omits the middle if the triple is a collider and includes it otherwise. The executable signature test reflects the two graph conditions. A signature mismatch yields a query on which `DAG.dSeparated` gives different answers. Lean verifies equivalence of the three orientations in the five-vertex Figure 2 by comparing every legal query and distinguishes a fourth orientation. General sufficiency, CPDAG construction and consistent extension are separate results. [Executable queries](../OpenCausalScience/Papers/VermaPearl1990/ExecutableQuery.lean) · [Figure 2](../OpenCausalScience/Papers/VermaPearl1990/Figure2.lean)

## Ali, Richardson and Spirtes (2009), MAG equivalence

[Proposition 3.6 and Figures 4 and 6](https://doi.org/10.1214/08-AOS626) separate adjacency and unshielded-collider agreement from the additional constraints in Theorem 3.7. Lean proves Proposition 3.6 when each nonadjacent pair has a separating set. In Figure 4, the first two graphs have identical separation signatures. The first and third share adjacencies and unshielded colliders, while their answers differ for one conditioning query. Both panels in Figure 6 verify equivalence by inspecting all legal singleton queries, and the displayed vertex sequence has different discriminating-path status between members. The general colliders-with-order algorithm remains a separate proof obligation. [Necessary conditions](../OpenCausalScience/Papers/AliRichardsonSpirtes2009/EquivalenceNecessary.lean) · [Figures 4 and 6](../OpenCausalScience/Papers/AliRichardsonSpirtes2009/Figures4And6.lean)

## Perković et al. (2018), DAG adjustment

[Definitions 3 and 6](https://jmlr.org/papers/v18/16-319.html) define forbidden vertices and the proper back-door graph. The JMLR PDF has SHA-256 `6030540bb09e1097924026140e1c3e8a6a96933a18c865df6bcc23495279947a`. In [DAGAdjustment.lean](../OpenCausalScience/Papers/PerkovicEtAl2018/DAGAdjustment.lean), `first_arrow_iff` proves reachability outside all treatments after the first arrow detects precisely the first arrows of proper causal paths. `forbidden_from_first_iff` proves the union of original-graph descendants of those arrows' heads equals the definition over every non-treatment vertex on the paths. `proper_backdoor_removes_iff` proves the corresponding deletion rule. These are general finite-DAG results. The mixed-graph amenability and representative arguments, the Python traversal correspondence, and causal adjustment itself have additional proof obligations.

## Kivva et al. (2022), Example 2

The [proceedings PDF, pp. 4–5](https://proceedings.mlr.press/v180/kivva22a/kivva22a.pdf) has SHA-256 `8e677c27d3f725e404b97123b7068e16ebf6f7c9be067241e41e0ac3763bb2ea`. [Example2.lean](../OpenCausalScience/Papers/KivvaEtAl2022/Example2.lean) encodes the two displayed binary kernels. At `do(X₁=0, X₂=1)` it finds `P(Y₁=0, Y₂=0)` equal to `2/9` and `5/18` when averaging the two equally weighted values of `U₂`. The printed values `4/9` and `5/9` are twice these probabilities. The outcomes still differ. The observational laws agree and give zero weight to off-diagonal treatment assignments, placing the example outside the positive model class of Definition 5.

## Witte et al. (2020), Figure 2B

*On Efficient Adjustment in Causal Graphs*, JMLR 21(246), Figure 2B (p. 8) and the text immediately after Proposition 6 (p. 9). The publisher PDF has SHA-256 `76b259d4937132f22b76899a81cdbd0a37299276eaddc05453b9b62adc160733`. [Publication and PDF](https://jmlr.org/papers/v21/20-175.html)

The text includes panel B among the panels with a valid adjustment set. The drawing has `X₁ → V₁ ← V₂ → Y → X₂` and boxes `V₂`. With treatments `{X₁, X₂}` and outcome `Y`, the corrected conclusion is that panel B admits no valid adjustment set. The proper noncausal path `X₂ ← Y` has no interior vertex, so it remains open under every allowed conditioning set. The absence of directed treatment-to-outcome paths also puts the panel outside the descendant premise of Proposition 6.

[Figure2B.lean](../OpenCausalScience/Papers/WitteEtAl2020/Figure2B.lean) proves the two directed reachability exclusions in `WitteFigure2B.noDirectedTreatmentToOutcome`. It checks all four candidates in `WitteFigure2B.candidateSetsFailToSeparate`. The mathematical conclusion about adjustment uses the graphical criterion with these checked premises. The CGA paper review recorded the discrepancy before this Lean check.

## Witte et al. (2020), Figure 2F

In panel F, Definition 5 removes `V₂` for the treatments `{X₁, X₂}` and outcome `Y`. Every directed path from `V₁` to `X₂` or `Y` visits the retained `X₁`. Definition 4 therefore gives the four projected arrows `V₁ → X₁`, `X₁ → X₂`, `X₁ → Y` and `X₂ → Y`, together with `X₂ ↔ Y`. [Definitions 4–5 and Figure 2F](https://jmlr.org/papers/volume21/20-175/20-175.pdf)

[Figure2F.lean](../OpenCausalScience/Papers/WitteEtAl2020/Figure2F.lean) checks the complete edge relations in `WitteFigure2F.directedEdges` and `WitteFigure2F.bidirectedEdges`. It excludes the two additional arrows printed in the projection. The remaining `X₂ ↔ Y` and the original directed edge `X₂ → Y` give the paper's adjustment conclusion by Proposition 6. The CGA paper review recorded both the projection discrepancy and the adjustment conclusion before this Lean check.

## Van der Zander, Liśkiewicz and Textor (2019, 2023), Lemma 2

The authors' corrigendum updates the complexity analysis of step 4 of ancestral-graph augmentation. The original proof loops over the bidirected components and links each pair of parents by an undirected edge. The same pair may be visited for many components. [Original paper, Lemma 2](https://arxiv.org/pdf/1803.00116v3), [2023 corrigendum](https://doi.org/10.1016/j.artint.2023.103938)

[AugmentationParentPairs.lean](../OpenCausalScience/Papers/VanDerZanderEtAl2023/AugmentationParentPairs.lean) models an explicit loop over unordered parent pairs. It bounds the number of checks by the number of components times the square of the maximum parent count. In a two-layer DAG with `2n` parents of each of `n` children, the loop checks `n²(2n−1)` pairs on `3n` vertices. `AugmentationParentPairs.exceeds_quadratic` proves that no constant times the square of the vertex count bounds these check counts. The statement concerns loop iterations, including checks for edges already present.

## Jeong, Tian and Bareinboim (2022), Lemma 4

Lemma 4 relates blocking causal paths to d-separation in the paper's causal-path graph. Consider the six arrows `X → A`, `X → B`, `B → C`, `C → A`, `A → Y` and `C → Y`. Their causal-path graph has the same arrows. Conditioning on `{A, B}` intercepts every directed path from `X` to `Y` and activates the collider on `X → A ← C → Y`. [Lemma 4 and Definition 2](https://papers.neurips.cc/paper_files/paper/2022/file/d67ac621411d6fa4dca682ce62f84ea7-Paper-Conference.pdf)

[Lemma4.lean](../OpenCausalScience/Papers/JeongEtAl2022/Lemma4.lean) checks the two outcomes on the same graph. For every finite DAG, `FrontDoorPathBlocking.deleted_graph_iff_avoiding_walk` proves that a directed walk remains after deleting edges incident to the blocked vertices if and only if the original graph has a directed walk avoiding those vertices. This is the path condition used by the directed search in the later finder. The verified statement addresses the first front-door condition. Testing a full front-door set also requires the two back-door path conditions. [Wienöbst, van der Zander and Liśkiewicz (2024), Algorithm 2](https://arxiv.org/pdf/2211.16468v4)

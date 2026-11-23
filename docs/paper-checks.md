# Paper checks

## Witte et al. (2020), Figure 2B

*On Efficient Adjustment in Causal Graphs*, JMLR 21(246), Figure 2B (p. 8) and the text immediately after Proposition 6 (p. 9). The publisher PDF has SHA-256 `76b259d4937132f22b76899a81cdbd0a37299276eaddc05453b9b62adc160733`. [Publication and PDF](https://jmlr.org/papers/v21/20-175.html)

The text includes panel B among the panels with a valid adjustment set. The drawing has `X₁ → V₁ ← V₂ → Y → X₂` and boxes `V₂`. With treatments `{X₁, X₂}` and outcome `Y`, the corrected conclusion is that panel B admits no valid adjustment set. The proper noncausal path `X₂ ← Y` has no interior vertex, so it remains open under every allowed conditioning set. The absence of directed treatment-to-outcome paths also puts the panel outside the descendant premise of Proposition 6.

[WitteFigure2B.lean](../OpenCausalScience/WitteFigure2B.lean) proves the two directed reachability exclusions and checks all four candidates in the displayed DAG: `∅`, `{V₁}`, `{V₂}` and `{V₁,V₂}`. The mathematical conclusion about adjustment uses the graphical criterion with these checked premises. The CGA paper review recorded the discrepancy before this Lean check.

## Witte et al. (2020), Figure 2F

In panel F, Definition 5 removes `V₂` for the treatments `{X₁, X₂}` and outcome `Y`. Every directed path from `V₁` to `X₂` or `Y` visits the retained `X₁`. Definition 4 therefore gives the four projected arrows `V₁ → X₁`, `X₁ → X₂`, `X₁ → Y` and `X₂ → Y`, together with `X₂ ↔ Y`. [Definitions 4–5 and Figure 2F](https://jmlr.org/papers/volume21/20-175/20-175.pdf)

[WitteFigure2F.lean](../OpenCausalScience/WitteFigure2F.lean) checks both complete edge relations and excludes the two additional arrows printed in the projection. The remaining `X₂ ↔ Y` and the original directed edge `X₂ → Y` give the paper's adjustment conclusion by Proposition 6. The CGA paper review recorded both the projection discrepancy and the adjustment conclusion before this Lean check.

## Van der Zander, Liśkiewicz and Textor (2019, 2023), Lemma 2

The authors' corrigendum updates the complexity analysis of step 4 of ancestral-graph augmentation. The original proof loops over the bidirected components and links each pair of parents by an undirected edge. The same pair may be visited for many components. [Original paper, Lemma 2](https://arxiv.org/pdf/1803.00116v3), [2023 corrigendum](https://doi.org/10.1016/j.artint.2023.103938)

[AugmentationParentPairs.lean](../OpenCausalScience/AugmentationParentPairs.lean) models an explicit loop over unordered parent pairs. It bounds the number of checks by the number of components times the square of the maximum parent count. In a two-layer DAG with `2n` parents of each of `n` children, the loop checks `n²(2n−1)` pairs on `3n` vertices. Lean proves that no constant times the square of the vertex count bounds these check counts. The statement concerns loop iterations, including checks for edges already present. It gives a lower bound for that operation count and an upper bound for the same loop model.

## Jeong, Tian and Bareinboim (2022), Lemma 4

Lemma 4 relates blocking causal paths to d-separation in the paper's causal-path graph. Consider the six arrows `X → A`, `X → B`, `B → C`, `C → A`, `A → Y` and `C → Y`. Their causal-path graph has the same arrows. Conditioning on `{A, B}` intercepts every directed path from `X` to `Y` and activates the collider on `X → A ← C → Y`. [Lemma 4 and Definition 2](https://papers.neurips.cc/paper_files/paper/2022/file/d67ac621411d6fa4dca682ce62f84ea7-Paper-Conference.pdf)

[FrontDoorPathBlocking.lean](../OpenCausalScience/FrontDoorPathBlocking.lean) checks the two outcomes on the same graph. For every finite DAG, it also proves that a directed walk remains after deleting edges incident to the blocked vertices if and only if the original graph has a directed walk avoiding those vertices. This is the path condition used by the directed search in the later finder. The verified statement addresses the first front-door condition. Testing a full front-door set also requires the two back-door path conditions. [Wienöbst, van der Zander and Liśkiewicz (2024), Algorithm 2](https://arxiv.org/pdf/2211.16468v4)

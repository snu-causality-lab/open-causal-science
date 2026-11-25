# Van der Zander, Liśkiewicz and Textor (2019, 2023), Lemma 2

<!-- topic: Graph separation -->
<!-- index-anchor: van-der-zander-liśkiewicz-and-textor-2019-2023-lemma-2 -->

[Paper index](../paper-checks.md)

The authors' corrigendum updates the complexity analysis of step 4 of ancestral-graph augmentation. The original proof loops over the bidirected components and links each pair of parents by an undirected edge. The same pair may be visited for many components. [Original paper, Lemma 2](https://arxiv.org/pdf/1803.00116v3), [2023 corrigendum](https://doi.org/10.1016/j.artint.2023.103938)

[AugmentationParentPairs.lean](../../OpenCausalScience/Papers/VanDerZanderEtAl2023/AugmentationParentPairs.lean) models an explicit loop over unordered parent pairs. It bounds the number of checks by the number of components times the square of the maximum parent count. In a two-layer DAG with `2n` parents of each of `n` children, the loop checks `n²(2n−1)` pairs on `3n` vertices. `AugmentationParentPairs.exceeds_quadratic` proves that no constant times the square of the vertex count bounds these check counts. The statement concerns loop iterations, including checks for edges already present.

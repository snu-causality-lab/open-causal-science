# Jeong, Tian and Bareinboim (2022), Lemma 4

<!-- topic: Adjustment -->
<!-- index-anchor: jeong-tian-and-bareinboim-2022-lemma-4 -->

[Paper index](../paper-checks.md)

Lemma 4 relates blocking causal paths to d-separation in the paper's causal-path graph. Consider the six arrows `X → A`, `X → B`, `B → C`, `C → A`, `A → Y` and `C → Y`. Their causal-path graph has the same arrows. Conditioning on `{A, B}` intercepts every directed path from `X` to `Y` and activates the collider on `X → A ← C → Y`. [Lemma 4 and Definition 2](https://papers.neurips.cc/paper_files/paper/2022/file/d67ac621411d6fa4dca682ce62f84ea7-Paper-Conference.pdf)

[Lemma4.lean](../../OpenCausalScience/Papers/JeongEtAl2022/Lemma4.lean) checks the two outcomes on the same graph. For every finite DAG, `FrontDoorPathBlocking.deleted_graph_iff_avoiding_walk` proves that a directed walk remains after deleting edges incident to the blocked vertices if and only if the original graph has a directed walk avoiding those vertices. This is the path condition used by the directed search in the later finder. The verified statement addresses the first front-door condition. Testing a full front-door set also requires the two back-door path conditions. [Wienöbst, van der Zander and Liśkiewicz (2024), Algorithm 2](https://arxiv.org/pdf/2211.16468v4)

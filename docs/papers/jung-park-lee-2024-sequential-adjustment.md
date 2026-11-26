# Jung, Park and Lee (2024), sequential adjustment correction

<!-- topic: Adjustment -->
<!-- index-anchor: jung-park-and-lee-2024-sequential-adjustment-correction -->

[Paper index](../paper-checks.md)

> **Author correction** · [Definition 7, forbidden descendants](#the-stagewise-forbidden-set) · The revised stagewise graph admits an adjustment on the example chain that the published definition excludes.

## The stagewise forbidden set

The proceedings' Definition 7 and the October 25, 2026 revision use different graphs for forbidden descendants. In the corrected Section 4 example `X₁ → Z → X₂ → Y`, block `{Z}` is admissible at stage 1. The published condition forbids `Z`. Removing incoming arrows into `X₂` leaves the corrected first-stage forbidden set empty. The corrected PDF has SHA-256 `e5f0a7a415aeff87f56bb4482cdbfe33800f3efd3e15a30649ac5c7980ae737c`. [Proceedings](https://proceedings.neurips.cc/paper_files/paper/2024/hash/233ff375b9795cd890f78a1f64459b8d-Abstract-Conference.html) · [Corrected version, pp. 7 and 10](https://www.sanghacklee.me/ai-corrected/SAC_AI_corrected_2026-10-25.pdf)

[SequentialAdjustment.lean](../../OpenCausalScience/Papers/JungEtAl2024/SequentialAdjustment.lean) checks rejection by the published rule and acceptance at both stages of the corrected rule. It proves the example's adjustment identity for normalized rational kernels under the chain factorization and checks both pruning examples in Section 4.1. The general graph lemma shows a forbidden descendant in the intervened DAG is still forbidden in the original DAG for a singleton treatment and outcome. The general finite rational formula now follows from the sequential stage equations, which are derived from exchangeability and consistency under the stated alignment and support conditions. Graphical sufficiency, necessity and finder correctness remain open here. [Sequential formula](../../OpenCausalScience/Papers/JungEtAl2024/SequentialFormula.lean)

The public [minSAC implementation at `a6d726e`](https://github.com/snu-causality-lab/minSAC/tree/a6d726e274e1ede25666f9655fff927722f6582d) accepts `({Z}, ∅)` on the Section 4 chain. On the second four-node example, it rejects `(∅, ∅)` and constructs `(∅, {C})`. These are replays of the two finite inputs in the corrected paper.

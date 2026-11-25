# Kim, Hwang and Lee (2024), DEDUCE-DEP correction

<!-- topic: Discovery -->
<!-- index-anchor: kim-hwang-and-lee-2024-deduce-dep-correction -->

[Paper index](../paper-checks.md)

The September 20, 2026 revision starts PC at conditioning-set size zero in Algorithm 3. Its Appendix D counts repeated recursive call occurrences in the all-independent case even when individual CI answers are cached. The corrected PDF has SHA-256 `bce54960fd555465693f078351dcc64a45637449b5d97a964a50ee06b74665cc`. [Proceedings](https://proceedings.mlr.press/v244/kim24a.html) · [Corrected version, pp. 6 and 19](https://www.sanghacklee.me/ai-corrected/deduce_dep_AI_corrected_2026-09-20.pdf)

[DeduceDep.lean](../../OpenCausalScience/Papers/KimEtAl2024/DeduceDep.lean) checks the missed edge deletion on the two-vertex empty DAG, derives the lower-order dependence rule from explicit CI axioms, and proves the `3m` branching recurrence above a fixed cutoff. For the all-independent tree without recursion-result memoization, the call count exceeds any fixed multiplier times a fixed natural base to the depth. The recurrence concerns the call tree, and the edge example concerns only the marginal deletion step. [Paper's software repository](https://github.com/snu-causality-lab/deduce-dep/tree/29393a10dde7b0bbe8f32d449c3e735f939321fa)

The public Python routine skips recursion when the same separating set is already recorded. On an empty four-vertex DAG with a size-two conditioning set and cutoff zero, it makes 16 calls including the initial call. The uncached recurrence gives 25 calls for that input. The replay counted entries to `deduce_dep` with exact independence answers. [Pinned Python routine](https://github.com/snu-causality-lab/deduce-dep/blob/29393a10dde7b0bbe8f32d449c3e735f939321fa/src/cddd/deductive_reasoning.py#L25)

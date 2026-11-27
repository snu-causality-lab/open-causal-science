# Lee and Honavar (2016), relational causal discovery under path semantics

<!-- topic: Discovery -->

Sanghack Lee and Vasant Honavar, *A Characterization of Markov Equivalence Classes of Relational Causal Models under Path Semantics*, UAI 2016, pp. 128–137. The companion formalizes a corrected RpCD learner for §4.1.1 and Theorem 9. The correction is unofficial and author review is pending. [Proceedings](https://proceedings.mlr.press/r14/university16d.html) · [Unofficial erratum, 2026-11-27](https://www.sanghacklee.me/ai-corrected/RpCD_CUT_AI_corrected_2026-11-27.pdf)

> **Verified counterexample** · [Section 4.1.1, six-label bound](#the-original-construction) · A 13-item skeleton has an unshielded triple that needs twelve middle-path labels from either endpoint.

## The original construction

[Anchors.lean](../../OpenCausalScience/Papers/LeeHonavar2016RpCD/Anchors.lean) checks all sixteen shared-block patterns and computes the middle and endpoint labels. [Witnesses.lean](../../OpenCausalScience/Papers/LeeHonavar2016RpCD/Witnesses.lean) proves `RpCD.actual_endpoints_unshielded` and `RpCD.GeneratingPaths.every_witness_has_twelve_middle_paths`. For the erratum's fixed generating dependencies, every realization with unshielded endpoints needs the full sharing pattern and exactly twelve middle-path labels at each endpoint. This refutes the six-label bound used in the original CUT construction. [PrintedRpCD.lean](../../OpenCausalScience/Papers/LeeHonavar2016RpCD/PrintedRpCD.lean) also proves `RpCD.supplement_line20_unreachable` for the conflicting bounds in supplemental Algorithm 1. The PDF documents the original review of the counterexample and constructor, and the proofs below also cover the corrected learner.

## Corrected learner

[RpCDBounded.lean](../../OpenCausalScience/Papers/LeeHonavar2016RpCD/RpCDBounded.lean) defines `RpCD.learnBounded` and proves `RpCD.learnBounded_correct_all_equivalent`. Given a finite role-free schema with distinct participating entity classes, a hop bound for the true dependencies, class-level acyclicity and an exact relational conditional-independence (CI) oracle, the learner recovers exactly the true dependency adjacencies. For adjacent attribute classes it returns a direction precisely when that direction holds in every well-formed model with the same relational CI relations. Equivalent models inherit the true model's hop bound.

- [Candidate enumeration](../../OpenCausalScience/Papers/LeeHonavar2016RpCD/RpCDCandidatePaths.lean) checks typed paths through the hop bound in both endpoint orders. [The skeleton proof](../../OpenCausalScience/Papers/LeeHonavar2016RpCD/RpCDPhaseOne.lean) preserves true dependencies using isolated paths and removes absent pairs using a parent separator.
- [Canonical unshielded triples](../../OpenCausalScience/Papers/LeeHonavar2016RpCD/CutSchedule.lean) are generated from the learned skeleton. The corrected search enumerates partial one-to-one matchings between the generating paths, completes vacant roles with fresh leaves and tests shielding. It covers every realizable ordered unshielded triple. The classifier checks middle membership in the same ground witness.
- [Completion](../../OpenCausalScience/Papers/LeeHonavar2016RpCD/RpCDCompletion.lean) tests possible directions by greedy sink elimination after classifying the triples. [The equivalence proof](../../OpenCausalScience/Papers/LeeHonavar2016RpCD/RpCDAllModels.lean) characterizes the compatible directions using ground-graph Markov equivalence.

The model uses simple paths of distinct items and [graphical CI](../../OpenCausalScience/Papers/LeeHonavar2016RpCD/RpCDGround.lean), with conditioned query endpoints removed before checking separation. The exact matching search has no verified polynomial bound in path length. The correctness theorem concerns the Lean reference learner. Verification of the historical Python implementation is outside its scope.

## Replay

Use the repository's Lean 4.36.0 toolchain.

```sh
lake build OpenCausalScience.Papers.LeeHonavar2016RpCD.RpCDBounded \
  OpenCausalScience.Papers.LeeHonavar2016RpCD.Witnesses \
  OpenCausalScience.Papers.LeeHonavar2016RpCD.PrintedRpCD
```

The top-level [axiom report](../../OpenCausalScience/Axioms.lean) lists transitive dependencies of the reported statements.

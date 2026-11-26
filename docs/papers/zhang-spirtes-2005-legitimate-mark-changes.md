# Zhang and Spirtes (2005), legitimate mark changes in directed MAGs

<!-- topic: Graph equivalence -->

Zhang and Spirtes describe transformations of directed maximal ancestral graphs. Lemma 1 treats changing `A → B` to `A ↔ B`. Lemma 2 characterizes a reversal accomplished by two such mark changes using equality of the external parent sets and equality of the spouse sets. [UAI paper, §2.2](https://www.cmu.edu/dietrich/philosophy/docs/spirtes/uai05.pdf)

- [LegitimateMarkChange.lean](../../OpenCausalScience/Papers/ZhangSpirtes2005/LegitimateMarkChange.lean) proves that the absence of an alternate directed path is exactly the ancestral condition for the head addition. With matching external parents and spouses, it establishes the alternate-path, incoming-neighbor, and discriminating-turn conditions of Lemma 1 used in this case.
- [MarkChangeSeparation.lean](../../OpenCausalScience/Papers/ZhangSpirtes2005/MarkChangeSeparation.lean) proves active-path and executable m-separation preservation under matching external parents and spouses. When a changed turn loses activation at `A`, the proof reroutes the walk through `B`, using its matching parents and spouses. The two-step result transfers the matching property to the reversed graph.
- [MarkChangeMarkedGraph.lean](../../OpenCausalScience/Papers/ZhangSpirtes2005/MarkChangeMarkedGraph.lean) gives the same separation result for singly marked graphs in `same_separations_of_matching` and `same_separations_of_reversal`.
- [ReversalCriterion.lean](../../OpenCausalScience/Papers/ZhangSpirtes2005/ReversalCriterion.lean) proves both directions of Lemma 2. Given an initial directed MAG and the two endpoint edits, `legitimate_reversal_iff_parent_and_spouse_sets` characterizes when both edits preserve the directed MAG conditions and the full m-separation relation. Necessity uses preservation of unshielded colliders and the ancestral restrictions. Sufficiency gives the ancestral and maximality properties as well as separation preservation.

The two-edit criterion is the local move used by CGA's native iterator. The transformation sequence between arbitrary equivalent representatives and the iterator's traversal guarantees are separate results. [CGA legitimate-reversal contract](https://github.com/snu-causality-lab/cga/blob/v0.2.0a1/c/include/cga/leg.h)

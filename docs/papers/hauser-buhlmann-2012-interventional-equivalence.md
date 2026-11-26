# Hauser and Bühlmann (2012), interventional Markov equivalence

<!-- topic: Experimental design -->

[Paper index](../paper-checks.md)

For each perfect-intervention target, the paper removes incoming arrows
to targeted variables. A set of targets is conservative when every
vertex is outside at least one target. Theorem 10 uses these cut graphs
to characterize equivalence over known targets. [Theorem 10, p. 2414](https://www.jmlr.org/papers/volume13/hauser12a/hauser12a.pdf#page=6)

## The graphical criteria in Theorem 10

[InterventionalEquivalence.lean](../../OpenCausalScience/Papers/HauserBuhlmann2012/InterventionalEquivalence.lean)
formalizes the graphical forms of (ii)–(iv) on finite labelled DAGs.

| Declaration | Conclusion |
| --- | --- |
| `cut_dConnections_iff_cut_signatures` | Agreement of graphical d-connections for each cut DAG is equivalent to agreement of the skeleton and v-structures in each regime. |
| `cut_signatures_iff_observational_and_cut_skeletons` | For conservative targets, the per-regime signatures agree exactly when the observational signatures and all cut skeletons agree. |
| `cut_skeleton_iff_crossing_directions` | With a shared observational skeleton, a cut skeleton records the directions of the arrows with exactly one endpoint in its target. This includes the assertion in Lemma 47. |
| `cutSignaturesMatch_iff` | The Boolean comparison is true exactly when every graphical d-connection query has the same answer in each regime. |

The proof reuses [Verma and Pearl's characterization](verma-pearl-1990-dag-equivalence.md).
A covered reversal between equally targeted endpoints disappears when
both endpoints are targeted and remains a covered reversal when neither
is targeted. This gives the direction from the observational signature
and the cut skeletons to per-regime equivalence. The probability
model equality in Theorem 10(i) and the characterization of
interventional essential graphs in Theorem 18 remain open here.
[Theorem 10 and Lemma 47 proofs](https://www.jmlr.org/papers/volume13/hauser12a/hauser12a.pdf#page=41)

## Figure 2

[Figure2.lean](../../OpenCausalScience/Papers/HauserBuhlmann2012/Figure2.lean)
checks all three seven-vertex DAGs. The observational signatures agree
pairwise. Under the observational regime and the intervention on
vertex 4, the signatures of `D` and `D₁` still agree. After cutting
arrows into vertex 4, the adjacency between 3 and 4 is absent in `D`
and present in `D₂`, which distinguishes their cut signatures.
[Figure 2, p. 2415](https://www.jmlr.org/papers/volume13/hauser12a/hauser12a.pdf#page=7)

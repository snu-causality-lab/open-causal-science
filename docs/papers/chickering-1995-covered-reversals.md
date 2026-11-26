# Chickering (1995), covered edge reversal

<!-- topic: Graph equivalence -->

Chickering's local transformation gives a way to move between equivalent DAGs while keeping their graphical independence model. The formalization uses this transformation to compare d-separation queries before and after a reversal. [UAI paper, Lemmas 1–2](https://arxiv.org/abs/1302.4938)

- [CoveredReversal.lean](../../OpenCausalScience/Papers/Chickering1995/CoveredReversal.lean) constructs a new acyclicity ranking for the reversed DAG when the endpoints have equal parent sets outside the pair. For any sets of query endpoints disjoint from the conditioning set, `Reversal.dConnection_iff` proves that the same d-connection holds in both DAGs. It compares the two ancestral moral graphs. When the old tail drops out of the ancestral set, each part of the walk through it is replaced by an adjacency or a co-parent edge.
- [FindEdge.lean](../../OpenCausalScience/Papers/Chickering1995/FindEdge.lean) proves Lemma 2. For graphs with the same skeleton and unshielded colliders, select a differently oriented edge whose head is earliest in the original topological order and whose tail is latest among the differently oriented parents of that head. The selected edge is covered.

- [Transformation.lean](../../OpenCausalScience/Papers/Chickering1995/Transformation.lean) proves the sequence existence in Theorem 2. `reversal_sequence` takes DAGs with the same d-separation queries and reaches the target edge function through covered reversals. `reversal_sequence_of_same_signature` obtains the sequence directly from the common skeleton and unshielded colliders. Each step reverses an edge that differs from the target, introduces no new differences and preserves d-separation.

The sequence theorem records the allowed steps and the final edge function. The proof uses the number of differing arrows as a decreasing measure. The greedy search operators and their large-sample guarantees belong to a separate paper. [Chickering's greedy search paper](https://jmlr.org/papers/v3/chickering02b.html)

# Perković (2020), partial causal ordering of MPDAG buckets

<!-- topic: Identification -->

Algorithm 1 removes sink buckets from the undirected components of the full graph, then retains their nonempty intersections with the requested vertex set. Lemma 3.5 states that the output is a bucket decomposition in which every edge between different buckets points forward. An undirected path establishing bucket membership can pass through vertices outside the selected set. [UAI 2020, Definition 3.3, Algorithm 1 and Lemma 3.5](https://proceedings.mlr.press/v124/perkovic20a/perkovic20a.pdf#page=5)

The Lean module proves that full-graph component labels exist and uses them as input to an executable sink-removal algorithm. `Components.arrow_to_bucket` derives the propagation of an external parent through a bucket from Meek R1 and R2. In a consistent DAG extension, the minimum topological rank in each bucket then increases along every arrow between buckets. `Components.exists_sink` gives a sink among any nonempty set of remaining buckets. [UAI 2020 supplement, Lemmas C.1 and C.2](https://proceedings.mlr.press/v124/perkovic20a/perkovic20a-supp.pdf#page=3)

`Components.pco_correct` proves that the algorithm returns each nonempty bucket intersection once, with all cross-bucket edges oriented forward. Its graph assumptions are a consistent DAG extension and closure under Meek R1 and R2. `R1R2Closed.of_meek_fixed` derives the latter condition at a fixed point of the existing Lean Meek rules. Decidable arrows provide the algorithm's edge tests, and an empty selected set yields an empty output. [PartialCausalOrder.lean](../../OpenCausalScience/Papers/Perkovic2020/PartialCausalOrder.lean)

`Figure4A.internal_arrow` checks that the arrow from `Y₁` to `X` is inside an undirected component. The path `Y₁ — V₁ — X` connects its endpoints. `Figure4A.pco_figure` computes the two ordered buckets `{Y₁, X}` and `{Y₂}` after excluding `V₁` from the selected set. [UAI 2020, Figure 4(a)](https://proceedings.mlr.press/v124/perkovic20a/perkovic20a.pdf#page=5)

# Richardson and Spirtes (2002), ancestral graph separation

<!-- topic: Graph separation -->

[Paper index](../paper-checks.md)

[Richardson and Spirtes (2002)](https://doi.org/10.1214/aos/1031689015), §3.4 and Figure 9, use endpoint marks to classify colliders. [MSeparation.lean](../../OpenCausalScience/Graph/MSeparation.lean) proves the reference evaluator returns true exactly when a simple m-connecting path exists in a finite graph with at most one marked edge per pair. In [Figure 9](../../OpenCausalScience/Papers/RichardsonSpirtes2002/Figure9.lean), the missing adjacency in (a) has no separator among the four legal conditioning sets, and the complete extension in (b) has the same separation answers for every singleton pair and legal conditioning set. The [authors' errata](https://sites.stat.washington.edu/tsr/website/documents/2002/annals-2002-errata.txt) address other locations. The CGA state-based search, graphs with bows, and the general augmentation theorem require separate correspondence proofs.

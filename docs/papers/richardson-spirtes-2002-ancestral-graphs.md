# Richardson and Spirtes (2002), ancestral graph separation

<!-- topic: Graph separation -->

[Paper index](../paper-checks.md)

[Richardson and Spirtes (2002)](https://doi.org/10.1214/aos/1031689015), §3.4 and Figure 9, use endpoint marks to classify colliders. [MSeparation.lean](../../OpenCausalScience/Graph/MSeparation.lean) proves the reference evaluator returns true exactly when a simple m-connecting path exists in a finite graph with at most one marked edge per pair. In [Figure 9](../../OpenCausalScience/Papers/RichardsonSpirtes2002/Figure9.lean), the missing adjacency in (a) has no separator among the four legal conditioning sets, and the complete extension in (b) has the same separation answers for every singleton pair and legal conditioning set. The [authors' errata](https://sites.stat.washington.edu/tsr/website/documents/2002/annals-2002-errata.txt) address other locations.

## Arrival-state search

The [mixed graph representation](../../OpenCausalScience/Graph/MixedGraph.lean)
records both endpoint marks. It permits parallel directed and bidirected
edges as in the [ADMG definitions in Richardson et al. (2023), Supplement A](https://doi.org/10.1214/22-AOS2253SUPP).
An endpoint of an undirected edge may have no incident arrowhead, as in
Richardson and Spirtes (2002), §3.1(ii). The path criterion follows §3.4.

[MixedPath.lean](../../OpenCausalScience/Graph/MixedPath.lean) proves that an
active walk admits a vertex-simple active path. At a repeated vertex, a
potentially blocked splice would require two arrowheads at a vertex outside the
conditioning ancestors. In that case the intervening loop must continue
along directed edges and cannot return with a tail. The proof handles bow
edges by tracking the incoming mark and retaining the chosen outgoing mark.

[MixedSeparationExecutable.lean](../../OpenCausalScience/Graph/MixedSeparationExecutable.lean)
checks directed ancestry, the initial arrivals, transitions and discovery of a
target. In [MixedSeparation.lean](../../OpenCausalScience/Graph/MixedSeparation.lean),
`MixedGraph.m_separated_iff_no_path` proves the resulting Boolean is equivalent
to the absence of a simple active path. The theorem covers the search rules
used by CGA. The [CGA proof map](../cga.md#compare-the-mixed-graph-arrival-search)
gives the replay against the released Python API and an independent path search.

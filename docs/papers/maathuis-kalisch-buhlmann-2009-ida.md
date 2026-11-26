# Maathuis, Kalisch and Bühlmann (2009), local IDA

<!-- topic: Graph equivalence -->

[Paper index](../paper-checks.md)

A true CPDAG describes the candidate DAGs for population IDA. Algorithm 3 keeps the compelled parents of one treatment and tries subsets of its undirected neighbors as additional parents. Lemma 3.1 says this choice can be extended to a candidate DAG exactly when it creates no new unshielded collider at the treatment. Theorem 3.2 compares the resulting sets of distinct possible effects. [Annals of Statistics, §3.2 and §8](https://doi.org/10.1214/09-AOS685) · [Article PDF](https://stat.ethz.ch/Manuscripts/buhlmann/AOS685.pdf#page=11)

[LocalIDA.lean](../../OpenCausalScience/Papers/MaathuisEtAl2009/LocalIDA.lean) proves Lemma 3.1 for the essential graph of any finite DAG. `no_new_collider_iff_clique` establishes that the selected neighbors must form a clique. A compelled parent is adjacent to every undirected neighbor of the treatment by the chain-component parent property. `no_new_collider_iff_extension` orders the selected clique before the treatment and the treatment before its remaining undirected neighbors. It uses the [essential-graph orientation theorem](andersson-madigan-perlman-1997-essential-graphs.md). `parent_readout_support_iff` proves the set-level step of Theorem 3.2 for any function of the parent set. The paper uses the appropriate population regression coefficient in its Gaussian setting. The Lean theorem takes that effect calculation as a function and leaves its statistical justification and sample consistency open.

One parent set can occur in several DAGs. The [joint-IDA companion](nandy-maathuis-richardson-2017-joint-ida.md#figure-2-and-example-3) replays a three-vertex case where one parent set occurs twice and another once in the full graph class. Local IDA reports both sets once.

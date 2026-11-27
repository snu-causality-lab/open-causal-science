# Levitz, Perlman and Madigan (2001), AMP p-separation

<!-- topic: Graphical Markov models -->

Michael Levitz, Michael D. Perlman and David Madigan, *Separation and Completeness Properties for AMP Chain Graph Markov Models*, Annals of Statistics 29(6), 1751–1784. The authors' 2003 correction supplies the complete Table 2 for §3 because the original table on p. 1757 was printed incompletely. [Original article](https://doi.org/10.1214/aos/1015345961) · [2003 correction, p. 348](https://doi.org/10.1214/aos/1046294468)

[Table2.lean](../../OpenCausalScience/Papers/LevitzEtAl2001/Table2.lean) encodes the corrected rule for an interior vertex of a trail. A head-no-tail vertex is active if it is conditioned on or has a directed descendant in the conditioning set. Any other vertex is active outside the conditioning set. A conditioned vertex also remains active if both incident trail edges are lines and an unconditioned parent points into it.

- `interior_active_iff` relates the Boolean rule to directed reachability and the parent exception. `dag_interior_active_iff` specializes it to the directed collider case in a DAG.
- `flag_separation_comparison` checks that the sole interior vertex on `A → B — C` is inactive unconditionally and active given `B`. The LWF moral separation check gives the opposite answers for the endpoints on the same graph, matching the [positive binary witnesses](andersson-et-al-2001-amp-chain-graphs.md).

The global equivalence between p-separation and augmentation in Theorem 4.1 and the Gaussian completeness result in Theorem 5.1 remain open in Lean.

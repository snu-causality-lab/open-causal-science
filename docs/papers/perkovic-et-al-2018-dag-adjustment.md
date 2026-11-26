# Perković et al. (2018), DAG adjustment

<!-- topic: Adjustment -->
<!-- index-anchor: perković-et-al-2018-dag-adjustment -->

[Paper index](../paper-checks.md)

[Definitions 3 and 6](https://jmlr.org/papers/v18/16-319.html) define forbidden vertices and the proper back-door graph. The JMLR PDF has SHA-256 `6030540bb09e1097924026140e1c3e8a6a96933a18c865df6bcc23495279947a`. In [DAGAdjustment.lean](../../OpenCausalScience/Papers/PerkovicEtAl2018/DAGAdjustment.lean), `first_arrow_iff` proves reachability outside all treatments after the first arrow detects precisely the first arrows of proper causal paths. `forbidden_from_first_iff` proves the union of original-graph descendants of those arrows' heads equals the definition over every non-treatment vertex on the paths. `proper_backdoor_removes_iff` proves the corresponding deletion rule. These are general finite-DAG results.

## Proper back-door deletion on mixed graphs

[MixedBackDoor.lean](../../OpenCausalScience/Papers/PerkovicEtAl2018/MixedBackDoor.lean) formalizes the edge deletion of Definition 6 for fully oriented mixed graphs with acyclic directed parts, supplying the directed-edge visibility predicate. `proper_backdoor_deletes_iff` identifies precisely the arrows removed. `bidirected_unchanged` proves that directed cuts also preserve a bidirected edge between the same endpoints. `path_connected_of_deleted` shows that a marked active path after deletion was already active in the original graph. Its collider-activation walks use only retained arrows.

Theorem 7 additionally needs the relation between open paths after deletion and the proper noncausal paths used in adjustment. Lemma 10 requires comparison with PAG definite-status paths, and Corollary 15 adds the constructive adjustment-set argument. These remain separate proof obligations, along with the probabilistic identification result and correspondence with the CGA traversal.

## Ancestral moralization

[Theorem 35](https://www.jmlr.org/papers/volume18/16-319/16-319.pdf#page=26) states the ancestral moralization criterion and cites Lauritzen et al. (1990), Proposition 3. In [Moralization.lean](../../OpenCausalScience/Graph/Moralization.lean), `Query.dConnection_iff_moralConnection` and `Query.dSeparation_iff_no_moralConnection` prove the equivalence for finite DAGs with both query sets disjoint from the conditioning set. Restrict to the ancestors of the three sets, make directed edges undirected, connect parents of each retained child, and delete the conditioned vertices. An undirected walk between the remaining query sets exists exactly when the original DAG has an active simple path between them. This mathematical reduction is the basis of the DAG branch in CGA's `d_separated_sets`. [CGA proof map](../cga.md)

The [executable formalization](../../OpenCausalScience/Graph/MoralizationExecutable.lean) computes the same graph construction and uses a finite worklist. `Query.dagMoralSeparated_eq_true_iff` relates the Boolean outcome to d-separation.

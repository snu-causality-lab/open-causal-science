# Perković et al. (2018), DAG adjustment

<!-- topic: Adjustment -->
<!-- index-anchor: perković-et-al-2018-dag-adjustment -->

[Paper index](../paper-checks.md)

[Definitions 3 and 6](https://jmlr.org/papers/v18/16-319.html) define forbidden vertices and the proper back-door graph. The JMLR PDF has SHA-256 `6030540bb09e1097924026140e1c3e8a6a96933a18c865df6bcc23495279947a`. In [DAGAdjustment.lean](../../OpenCausalScience/Papers/PerkovicEtAl2018/DAGAdjustment.lean), `first_arrow_iff` proves reachability outside all treatments after the first arrow detects precisely the first arrows of proper causal paths. `forbidden_from_first_iff` proves the union of original-graph descendants of those arrows' heads equals the definition over every non-treatment vertex on the paths. `proper_backdoor_removes_iff` proves the corresponding deletion rule. These are general finite-DAG results.

## Proper back-door deletion on mixed graphs

[MixedBackDoor.lean](../../OpenCausalScience/Papers/PerkovicEtAl2018/MixedBackDoor.lean) formalizes the edge deletion of Definition 6 for fully oriented mixed graphs with acyclic directed parts, supplying the directed-edge visibility predicate. `proper_backdoor_deletes_iff` identifies precisely the arrows removed. `bidirected_unchanged` proves that directed cuts also preserve a bidirected edge between the same endpoints. `path_connected_of_deleted` shows that a marked active path after deletion was already active in the original graph. Its collider-activation walks use only retained arrows.

## Blocking and separation on fully oriented graphs

[ProperPathBlocking.lean](../../OpenCausalScience/Papers/PerkovicEtAl2018/ProperPathBlocking.lean) proves the path-blocking equivalence in [Theorem 7](https://jmlr.org/papers/volume18/16-319/16-319.pdf) for fully oriented graphs, including DAGs and MAGs. `forbidden_iff_forbidden_on_paths` identifies the descendants of first-arrow heads with the descendants of all non-treatment vertices on proper directed paths. `proper_noncausal_path_iff_backdoor_connection` proves that there is an active proper noncausal path in the original graph exactly when there is an active path in the proper back-door graph. The treatment and outcome sets are disjoint. Amenability uses the supplied visibility predicate, and the conditioning set avoids the forbidden set. The proof preserves the marks of separate edges at the same endpoints.

## Definite-status paths in MAG representatives

[PAGBlocking.lean](../../OpenCausalScience/Papers/PerkovicEtAl2018/PAGBlocking.lean) proves `noncausal_path_in_representative`, the non-blocking direction used in Lemma 10. A definite-status active noncausal PAG path remains active and noncausal on the same vertex sequence in each MAG representative. A circle on an unshielded triple supplies a representative with a tail at that endpoint. The [unshielded collider invariance result](ali-richardson-spirtes-2009-mag-equivalence.md) then shows that the triple remains a noncollider in every representative. The representation premises include invariant marks, adjacencies, maximality and shared m-separations.

The reverse transfer of a shortest, minimum-distance-to-conditioning MAG path to a definite-status PAG path follows Lemmas 50–52 and remains open in this library. Corollary 15 also needs the constructive adjustment-set argument of Theorem 14. The probabilistic identification result and the correspondence with CGA's PAG traversal have separate proof obligations.

## Ancestral moralization

[Theorem 35](https://www.jmlr.org/papers/volume18/16-319/16-319.pdf#page=26) states the ancestral moralization criterion and cites Lauritzen et al. (1990), Proposition 3. In [Moralization.lean](../../OpenCausalScience/Graph/Moralization.lean), `Query.dConnection_iff_moralConnection` and `Query.dSeparation_iff_no_moralConnection` prove the equivalence for finite DAGs with both query sets disjoint from the conditioning set. Restrict to the ancestors of the three sets, make directed edges undirected, connect parents of each retained child, and delete the conditioned vertices. An undirected walk between the remaining query sets exists exactly when the original DAG has an active simple path between them. This mathematical reduction is the basis of the DAG branch in CGA's `d_separated_sets`. [CGA proof map](../cga.md)

The [executable formalization](../../OpenCausalScience/Graph/MoralizationExecutable.lean) computes the same graph construction and uses a finite worklist. `Query.dagMoralSeparated_eq_true_iff` relates the Boolean outcome to d-separation.

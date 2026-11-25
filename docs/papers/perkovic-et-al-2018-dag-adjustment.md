# Perković et al. (2018), DAG adjustment

<!-- topic: Adjustment -->
<!-- index-anchor: perković-et-al-2018-dag-adjustment -->

[Paper index](../paper-checks.md)

[Definitions 3 and 6](https://jmlr.org/papers/v18/16-319.html) define forbidden vertices and the proper back-door graph. The JMLR PDF has SHA-256 `6030540bb09e1097924026140e1c3e8a6a96933a18c865df6bcc23495279947a`. In [DAGAdjustment.lean](../../OpenCausalScience/Papers/PerkovicEtAl2018/DAGAdjustment.lean), `first_arrow_iff` proves reachability outside all treatments after the first arrow detects precisely the first arrows of proper causal paths. `forbidden_from_first_iff` proves the union of original-graph descendants of those arrows' heads equals the definition over every non-treatment vertex on the paths. `proper_backdoor_removes_iff` proves the corresponding deletion rule. These are general finite-DAG results. The mixed-graph amenability and representative arguments, the Python traversal correspondence, and causal adjustment itself have additional proof obligations.

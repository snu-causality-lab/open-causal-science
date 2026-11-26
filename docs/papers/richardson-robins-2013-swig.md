# Richardson and Robins (2013), single-world intervention graphs

<!-- topic: Counterfactual identification -->

[Paper index](../paper-checks.md)

[CSSS Working Paper 128, 30 April 2013](https://csss.uw.edu/Papers/2013/wp128.pdf) defines a single-world intervention template in §3.3.1. Each treatment variable is split into a random half and a fixed half. The random half receives the original incoming arrows. The fixed half carries the original outgoing arrows. A random vertex is labeled by the values of the fixed vertices that reach it along directed paths.

## Splitting and directed paths

[NodeSplitting.lean](../../OpenCausalScience/Papers/RichardsonRobins2013/NodeSplitting.lean) represents the random copy of every original vertex and makes fixed copies available only for selected intervention targets. `translated_edge_iff` and `no_incoming_fixed` establish the edge correspondence in Propositions 6 and 7. `original_walk` maps every template path to an original path, preserving acyclicity. `random_walk_iff` identifies the random-only directed paths with paths in the original graph after deleting the arrows leaving the treatment targets.

`label_monotone_along_walk` proves the inclusion of labels along a directed path between random vertices in Proposition 8. `in_label_iff` characterizes label membership by an original directed path from the treatment with all interior vertices outside the intervention set. The endpoint can be the random half of another treatment target. The Lean graph and label statements concern the template before fixed values are assigned. Theorem 12’s Markov implication from factorization and the counterexample distribution in Theorem 19 remain open here. [Construction and Propositions 4–9](https://csss.uw.edu/Papers/2013/wp128.pdf#page=27)

## Examples

[Figure2.lean](../../OpenCausalScience/Papers/RichardsonRobins2013/Figure2.lean) replays the graph shared by the `x=0` and `x=1` panels of Figure 2. The fixed `x` labels the random outcome `Y(x)`. The random `X` has no directed path to that outcome. `successive_treatments` also checks `A → B → Y` when both `A` and `B` are split. The fixed `a` labels the random `B(a)`, and only `b` labels the random `Y(b)`. The random half of `B` receives the arrow from `a`; the outgoing arrow to `Y` starts at the fixed half of `B`. [Figure 2](https://csss.uw.edu/Papers/2013/wp128.pdf#page=10)

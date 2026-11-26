# Pearl (1995), action and observation exchange

<!-- topic: Identification -->

[Paper index](../paper-checks.md)

Theorem 4.1, Rule 2, Equation (11) equates the action and observation
conditionals under a separation condition in the graph with incoming
arrows into the fixed variables and outgoing arrows from the exchanged
variables removed. [AISTATS pre-proceedings](https://proceedings.mlr.press/r0/pearl95a.html)

[RuleTwo.lean](../../OpenCausalScience/Papers/Pearl1995/RuleTwo.lean)
proves the probability step for a finite response model with a common
exogenous law. The other interventions are already fixed. In the set
regime, the model keeps the natural value of the exchanged variables as a
separate response. Lean derives from the response definitions that, when
the natural value equals the setting, the outcome and covariate events
agree on each unit.
`Model.supported_action_observation_exchange` then proves the equality of
the two conditionals from conditional independence in the set regime and
positive conditioning masses.

The binary example has a common cause `W` of `Z` and `Y` and an
arrow from `Z` to `Y`. Lean checks the independence and support premises
for every conditioning cell. Without conditioning on `W`, the risk
under setting `Z` to zero is `1/2`, and the risk among units with
observed `Z=0` is `1/4`.

## Deriving the independence premise from the cut graph

[RuleTwoGraph.lean](../../OpenCausalScience/Papers/Pearl1995/RuleTwoGraph.lean)
uses a ranked finite binary structural model. Earlier actions are already
applied. The model has independent finite noise laws for a treatment
block, an outcome block, and the observed roots. The observed roots'
values determine the root input, so conditioning on the root input is
conditioning on the observed roots.

`SCM.natural_eq_set` proves that setting a variable to its own natural
value preserves every response. The exchanged variable also keeps its
natural value when its children receive a set value.
`SCM.supported_rule_two_of_separated_skeleton` removes the exchanged
variable's outgoing arrows and the conditioned roots, then uses the
undirected graph of remaining arrows. The two noise blocks follow its
connected components on the exchanged variable's side and the remaining
side. If the outcome lies in the remaining side, the cut makes the
natural exchanged response and the set outcome functions of separate
noise blocks at each conditioned root value. The factorization of the
conditioned masses yields the exchange identity on supported cells.

This graph condition uses separation in the entire remaining skeleton
and conditions only on observed roots. Pearl's theorem allows general
d-separation, including paths blocked by collider structure and
conditioning on nonroots.

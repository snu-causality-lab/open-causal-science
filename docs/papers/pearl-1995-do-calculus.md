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
positive conditioning masses. Deriving this independence from separation
in the manipulated causal graph is a separate step.

The binary example has a common cause `W` of `Z` and `Y` and an
arrow from `Z` to `Y`. Lean checks the independence and support premises
for every conditioning cell. Without conditioning on `W`, the risk
under setting `Z` to zero is `1/2`, and the risk among units with
observed `Z=0` is `1/4`.

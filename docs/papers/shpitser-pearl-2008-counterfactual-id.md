# Shpitser and Pearl (2008), counterfactual identification

<!-- topic: Counterfactual identification -->

[Paper index](../paper-checks.md)

The counterfactual identification problem in §4 takes the complete
family of single-world intervention distributions, denoted `P_*`, as
input. `ID*` handles conjunctions of counterfactual events. `IDC*`
handles conditional queries and distinguishes nonidentification from
zero evidence mass. The earlier publication appeared at UAI 2007.
[UAI 2007](https://arxiv.org/abs/1206.5294) ·
[JMLR 2008, §4 and Figure 12](https://www.jmlr.org/papers/volume9/shpitser08a/shpitser08a.pdf#page=21)

## Shared exogenous variables and merging

[ParallelWorlds.lean](../../OpenCausalScience/Papers/ShpitserPearl2008/ParallelWorlds.lean)
uses the same exogenous unit for every intervention world. For copies of
one binary variable, `response_eq_of_matching_parents` checks Lemma 24
when the shared mechanism is free in both worlds and its parent inputs
match. `merged_response_eq` evaluates the chosen representative's
mechanism and reads its parents through the representative map, as in
Lemma 25. `merge_preserves_mass` proves that the resulting rewiring and
renaming preserve any finite rational query mass on the evidence event.
Equal copies assigned distinct values give an empty conjunction.
[Figure 10 and Lemmas 24–25](https://www.jmlr.org/papers/volume9/shpitser08a/shpitser08a.pdf#page=18)

[Figure9.lean](../../OpenCausalScience/Papers/ShpitserPearl2008/Figure9.lean)
checks every merge in Figure 11. In particular, the factual `Z`, `Z_x`,
and `Z_d` have the same response when the observed `D` equals the value
given to `D` in the intervention world. The proof checks this equality
on that evidence event for every unit. The relabelled query replaces
`Z_d` by factual `Z` and has the same joint mass with `D = d`.
[Figures 9 and 11](https://www.jmlr.org/papers/volume9/shpitser08a/shpitser08a.pdf#page=20)

## The worked ID* and IDC* trace

[Figure9Trace.lean](../../OpenCausalScience/Papers/ShpitserPearl2008/Figure9Trace.lean)
starts with 15 observed world copies, including the intervention
constants. The three merge stages retain 13, 10, and 9 copies. The
ancestral restriction has the six vertices and parent lists of Figure
9(c). In the exchange tests, deleting outgoing edges from `D` or `Z`
separates that candidate from `Y_x`. The shared exogenous input leaves
factual `X` connected to both `Y_x` in Figure 9(c) and `Y_x,z` in Figure
9(d). Joint `ID*` then splits the three random nodes into the district
of `W_x,z` and the district of `X, Y_x,z`. The two single-district
calls produce the settings for the single-world terms `P_x(w)` and
`P_{z,w}(y,x′)`. `idc_star_worked_formula` in
[Figure9.lean](../../OpenCausalScience/Papers/ShpitserPearl2008/Figure9.lean)
checks the final ratio of the sum of their products to `P(x′)` for
binary endogenous outcomes, finite rational independent noise blocks,
and nonzero original evidence mass.
[Worked example and Figure 12](https://www.jmlr.org/papers/volume9/shpitser08a/shpitser08a.pdf#page=23)

## Base cases and a nonidentification example

[CounterfactualDecision.lean](../../OpenCausalScience/Papers/ShpitserPearl2008/CounterfactualDecision.lean)
checks the empty conjunction and effectiveness cases in lines 1–3.
For a simplified single-district factor, it checks the assignment conflict
of line 8, with a subscript value compared against other subscript and
event values. The line 9 assignment includes every supplied setting.
`union_action_mass` checks the kernel equality when that common setting
agrees on every atom's ancestry in its original cut graph. The
conditional evaluator returns no probability exactly when the evidence
has zero mass.

[WGraph.lean](../../OpenCausalScience/Papers/ShpitserPearl2008/WGraph.lean)
checks a binary example of the w-graph obstruction in Lemma 27. Two
models on `X → Y` agree on every observational and interventional cell
and have positive observational cells. Their values for
`P(Y_0 = 0, Y_1 = 1)` are `1/8` and `3/8`. For the conditional query
`P(Y_0 = 0 | Y_1 = 1)` with supported evidence, the values are `1/4`
and `3/4`. The single-district test reports the conflict between the
two settings of `X`. The full `make-cg` construction and the general
soundness and completeness theorems in §4 are separate from these
checked steps. [Lemmas 27 and 42, and Theorems 26 and 31](https://www.jmlr.org/papers/volume9/shpitser08a/shpitser08a.pdf)

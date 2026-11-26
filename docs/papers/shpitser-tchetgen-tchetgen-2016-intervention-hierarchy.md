# Shpitser and Tchetgen Tchetgen (2016), a graphical hierarchy of interventions

<!-- topic: Path-specific effects -->

[Paper index](../paper-checks.md)

## Edge g-formula

Lemma 5.6 gives the joint response to an edge intervention as a product
of the observational conditionals. In each factor, a clamped incoming
edge supplies its fixed input. Other incoming edges supply the value of
the parent in the response row. The model is the multiple-world
NPSEM with independent errors. [Annals of Statistics, Lemma 5.6 and Equation (5)](https://pmc.ncbi.nlm.nih.gov/articles/PMC5597261/)

[EdgeGFormula.lean](../../OpenCausalScience/Papers/ShpitserTchetgenTchetgen2016/EdgeGFormula.lean)
implements ranked finite binary DAGs with an independently sampled
finite exogenous coordinate at each vertex and rational weights.
`evaluate_eq_iff_local` proves that the local equations at a candidate
row hold exactly when the recursive response equals that row.
`edge_joint_mass_eq_product` factors the actual mass over independent
noises. `observed_conditional_eq_local_mass` obtains the local response
probability from the same model's observational law. Its proof uses
the fact that changing a vertex's noise cannot change any of its
parents. `edge_g_formula` composes the equalities at parent assignments
with nonzero observed mass.

## Reduction from path interventions

[PathReduction.lean](../../OpenCausalScience/Papers/ShpitserTchetgenTchetgen2016/PathReduction.lean)
checks the recursive substitution in Lemma 5.7. A local path setting
can distinguish two uses of the same parent in different downstream
contexts. If each incoming setting reached from the outcome agrees
with the induced edge setting, `path_response_eq_edge_response`
proves equality of the responses on every unit. Both recursions stop
upstream at a fixed input. [EdgeConsistency.lean](../../OpenCausalScience/Papers/ShpitserTchetgenTchetgen2016/EdgeConsistency.lean)
uses the listed assigned prefixes to induce edge settings. It proves
that coverage of relevant paths and agreement on each first edge imply
the compatible substitution. [Figure2A.lean](../../OpenCausalScience/Papers/ShpitserTchetgenTchetgen2016/Figure2A.lean)
checks the three cases in §5.3. The common `W → A` edge has one target
value when both downstream paths receive the same value. The lone
mediator path leaves the direct route uncovered, and giving the routes
different values fails agreement. Theorem 5.2's general nonidentification
result for edge-inconsistent paths requires a separate proof.
[Annals of Statistics, §5.3](https://arxiv.org/pdf/1411.2127#page=26)

# Foygel, Draisma and Drton (2012), the half-trek criterion

<!-- topic: Linear graphical models -->

[Original paper, Examples 1–2 and Figure 1](https://arxiv.org/abs/1107.5552)

The [Lean companion](../../OpenCausalScience/Papers/FoygelEtAl2012/InstrumentalVariable.lean)
uses the centered instrumental-variable model of Example 1. The instrument
has zero covariance with both downstream error terms. The errors at the
treatment and outcome can be correlated.

`example1_coefficients` proves the two coefficient ratios in Example 2 over
rational-valued linear moments. It assumes that the instrument’s variance and
its covariance with the treatment are nonzero. The proof uses linearity of
covariance in the second argument and the structural equations.

The general graphical half-trek criterion, the max-flow reduction and
recovery of the full error covariance matrix remain separate proof targets.

# Drton (2009), discrete chain graph models

<!-- topic: Graphical Markov models -->

Mathias Drton, *Discrete Chain Graph Models*, Bernoulli 15(3), 736–753. Section 2.2 distinguishes four block-recursive interpretations of the same chain graph. [Published article](https://doi.org/10.3150/08-BEJ172) · [Author version, arXiv:0909.0843v1](https://arxiv.org/pdf/0909.0843)

[ChainMarkov.lean](../../OpenCausalScience/Graph/ChainMarkov.lean) encodes the choices among C1, C2a/C2b and C3a/C3b for types I (LWF), II (AMP), III (dual AMP) and IV (multivariate regression). `check_iff` relates the Boolean test to its generated component and subset statements. `CIStatement.block_binary_check_iff` relates it to rational contingency-table cross-products on binary variables. This is the finite cell formulation of the independence equations used in the [Dawid companion](dawid-1979-conditional-independence.md).

[Example3.lean](../../OpenCausalScience/Papers/Drton2009/Example3.lean) instantiates Fig. 3 and Example 3 on p. 741, with `1 → 3` and `2 — 3 — 4`. The four exact rational distributions satisfy the following memberships. `laws_positive_normalized` proves full support and unit mass. `type_i_membership` through `type_iv_membership` verify every entry using the block-recursive test. The distributions are constructed for this check.

| Distribution | I | II | III | IV |
| --- | --- | --- | --- | --- |
| `law .I` | yes | no | no | no |
| `law .II` | no | yes | no | no |
| `law .III` | no | no | yes | no |
| `law .IV` | no | no | no | yes |

The description of `nd_D(τ)` on p. 739 prints a path directed from the candidate `τ̄` to `τ`. The outgoing-path reading agrees with the adjacent Example 1, where the nondescendants of `{1}` are `{2}` and omit the downstream components. The formalization uses that reading.

The paper's smoothness and curved-exponential-family results remain open in Lean. The witness check concerns the four interpretations on the graph in Fig. 3.

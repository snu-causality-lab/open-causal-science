# Correa, Lee and Bareinboim (2021), nested counterfactual identification

<!-- topic: Counterfactual identification -->

[Paper index](../paper-checks.md)

The references below use the NeurIPS 2021 proceedings. The March 2025
revision of technical report R-79 numbers the unnesting identity as
equation (22) and the conditional reduction as equation (25).
[Proceedings](https://proceedings.neurips.cc/paper_files/paper/2021/hash/36bedb6eb7152f39b16328448942822b-Abstract.html) ·
[Technical report R-79](https://causalai.net/r79.pdf)

## Unnesting equation

[Unnesting.lean](../../OpenCausalScience/Papers/CorreaLeeBareinboim2021/Unnesting.lean)
proves equation (21) by partitioning the nested event by the
assignment of the natural intervention. The response with that
assignment and the natural value both use the same exogenous unit.
The assignment list contains every realized assignment exactly
once. The theorem applies to finite rational masses and arbitrary
decidable assignment types. `ranked_scm_unnesting` specializes it to
finite ranked binary SCMs, where inherited settings may themselves
vary across units.

`identified_nested_of_identified_joint_cells` proves the sufficient
direction. Agreement of the supplied data gives agreement of the nested
cell if every joint summand is identified from those data.
[Theorem 4 and equation (21)](https://proceedings.neurips.cc/paper/2021/file/36bedb6eb7152f39b16328448942822b-Paper.pdf#page=8)

## CTFIDU source selection

[SourceKernels.lean](../../OpenCausalScience/Papers/CorreaLeeBareinboim2021/SourceKernels.lean)
implements the search in Algorithm 1, lines 5–11, once the consistent
ctf-factor and its district target have been supplied. Each candidate
source is represented by its free vertices. `find_source_iff` proves
that the search succeeds exactly when some supplied source retains
the target and a legal fixing order in that source reaches the target.
`selected_source_returns_kernel` proves that a successful plan
returns the target kernel, given the source district kernel and
Tian and Pearl's two kernel-operation identities.

[Figure5.lean](../../OpenCausalScience/Papers/CorreaLeeBareinboim2021/Figure5.lean)
replays Figure 5(a). Observation alone reaches the ancestor fixed
point for the factor on `Z`. Adding a source that intervenes on `X`
allows the same search to recover that factor. The source search
recovers the factor on `Y` from observation. As in equation (17),
the consistent factor and the available data both matter.
[Figure 5 and equation (17)](https://proceedings.neurips.cc/paper/2021/file/36bedb6eb7152f39b16328448942822b-Paper.pdf#page=7)

## Supported conditional normalization

[ConditionalNormalization.lean](../../OpenCausalScience/Papers/CorreaLeeBareinboim2021/ConditionalNormalization.lean)
verifies the normalization in Algorithm 2, line 4, when the
retained factorization holds and the evidence has positive mass.
The function returns `none` when the denominator is unsupported.

[Figure6.lean](../../OpenCausalScience/Papers/CorreaLeeBareinboim2021/Figure6.lean)
proves equation (23) for Figure 6(a) with binary observed variables,
finite rational exogenous laws, and a private response block for
`Y` independent of the common `X,Z` block. When both evidence
events have positive mass, the cross-world conditional equals the
observational conditional at `X=x,Z=z`.

The verified statements cover the unnesting identity and sufficient
direction, the consistent-factor source search, and supported
conditional normalization. The converse of unnesting and the general
ancestral-component reduction require separate arguments. For the
ordinary conditional identification problem with multiple sources,
Kivva, Etesami and Kiyavash (2023) discuss positivity and give a
conditional-to-joint reduction. [Algorithm 2 and Figure 6](https://proceedings.neurips.cc/paper/2021/file/36bedb6eb7152f39b16328448942822b-Paper.pdf#page=9) ·
[Kivva et al., §3](https://proceedings.mlr.press/v216/kivva23a.html)

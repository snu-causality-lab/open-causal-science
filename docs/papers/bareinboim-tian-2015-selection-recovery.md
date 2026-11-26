# Bareinboim and Tian (2015), causal effect recovery from selection bias

<!-- topic: Selection recovery -->

[Paper index](../paper-checks.md)

The paper studies recovery of the population interventional
distribution from the selected observational joint at one fixed
selection event. Theorem 2 gives a complete criterion in Markovian
models. Figure 4 gives the RC recursion for graphs that also have
latent confounding. [AAAI proceedings, pp. 3475–3481](https://doi.org/10.1609/aaai.v29i1.9679) ·
[Author report R-445](https://ftp.cs.ucla.edu/pub/stat_ser/r445.pdf)

## The selected-only RC recursion

[RC.lean](../../OpenCausalScience/Papers/BareinboimTian2015/RC.lean)
implements the Figure 4 plan on a finite mixed graph. It first retains
the directed ancestors of the target district and the selection
vertex. A district is eligible for extraction when it contains no
ancestor of selection. An eligible district containing the target is
handed to the ordinary `Identify` procedure. Otherwise, RC divides
by the product of the eligible district factors and recurses with
their vertices removed from the random set. Those vertices may
remain fixed arguments of the kernel.

`peel_shrinks_iff` proves that this removal strictly shrinks the
current graph exactly when the eligible list is nonempty.
`plan_blocks_here_iff` connects the stopping branch to the two
graph tests in Figure 4. `successful_execution_returns_kernel`
proves that a successful run gives the population kernel for the
target when the ancestral marginalization, district extraction,
and division operations satisfy their stated local kernel laws.
[Figure 4 and Theorem 3](https://ojs.aaai.org/index.php/AAAI/article/download/9679/9538#page=6)

[KernelIdentities.lean](../../OpenCausalScience/Papers/BareinboimTian2015/KernelIdentities.lean)
formalizes the finite rational calculations in Lemma 3 and
Theorem 3. A bounded topological rank can put all current ancestors
of selection before every vertex of an eligible district. Once the
selection-parent assignment is fixed across adjacent prefix fibers,
the same selection multiplier factors out of both sums and cancels
in every supported prefix ratio. The product of these selected
ratios gives the population product. Dividing out supported recovered
district factors leaves the remaining population kernel with its
original selection multiplier. A recovered effect that is invariant
in leftover fixed arguments can average them against a normalized
available law. [Equations (16)–(20)](https://ojs.aaai.org/index.php/AAAI/article/download/9679/9538#page=5) ·
[Equations (23)–(26)](https://ojs.aaai.org/index.php/AAAI/article/download/9679/9538#page=6)

## Figure 5

[Figure5.lean](../../OpenCausalScience/Papers/BareinboimTian2015/Figure5.lean)
checks that after intervening on `X`, the effect calculation requires
the single district `{Y}` in all three panels.

| Panel | Lean trace |
| --- | --- |
| (a) | Every district intersects the ancestor set of `S`, and RC stops without a formula. |
| (b) | The eligible district `{W₁,X,Y}` contains `Y`. Ordinary `Identify` restricts to `{X,Y}`, extracts `{Y}`, and reaches the target. |
| (c) | RC divides by the factor on `{X}`, marginalizes `W₁` after it stops being an ancestor, and extracts `{Y}` in the smaller graph. |

[Figure 5 and worked traces](https://ojs.aaai.org/index.php/AAAI/article/download/9679/9538#page=6)

## Figure 3(c–d)

[Figure3.lean](../../OpenCausalScience/Papers/BareinboimTian2015/Figure3.lean)
checks that removing arrowheads into `X` makes `Y` and `S`
m-separated given `X`, while RC still stops in the original graph.
Two compatible models use a shared exogenous response for the
observed variables and an independent selection draw. All
observational cells at either value of `S` are positive. Both models
give the same selected law and the same selection probability
`1/2`. The population probability of outcome one under either
intervention on `X` is `1/2` in the first model and `7/12` in the
second. This verifies the example's joint obstruction using the
original query. [Figure 3(c–d)](https://ojs.aaai.org/index.php/AAAI/article/download/9679/9538#page=5)

The formalized scope is the selected-only recursion, its local
identities, and the displayed examples. Theorem 2's general
necessity direction and recovery from an external population
marginal are separate. CGA's selected-only API reports a procedure
failure as `RecoveryNotEstablished`; the external-data API uses the
later IDSB and RCE procedures. [CGA selection recovery](https://github.com/snu-causality-lab/cga/blob/v0.2.0a1/docs/reference/PUBLISHED_IDENTIFICATION.md#selection-recovery)

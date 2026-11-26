# Kocaoglu, Jaber, Shanmugam and Bareinboim (2019), controlled soft interventions

<!-- topic: Discovery -->

The input is a causal DAG with observed and latent vertices and a common
family of known controlled intervention targets. Definition 3 adds a
fresh root for each distinct symmetric difference of the target sets.
Its children are exactly the variables in that difference. The causal
arrows stay in the graph. [Definition 3 and Figure 2](https://proceedings.neurips.cc/paper/2019/file/c3d96fbd5b1b45096ff04c04038fff5d-Paper.pdf#page=6)

## Augmentation and ordinary d-separation

[Augmentation.lean](../../OpenCausalScience/Papers/KocaogluEtAl2019/Augmentation.lean)
constructs canonical target differences and proves that each recorded
difference comes from a pair of regimes and vice versa. `addRoots`
preserves base arrows, implements the stated root children and prevents
incoming edges at fresh roots. A topological rank witnesses acyclicity.

`dconnected_with_roots_conditioned_iff` proves the pairwise form of
Proposition 1(1) for arbitrary finite DAGs and root child sets. An active
walk between base vertices cannot pass through a conditioned root. A
base vertex also cannot have a new root as a descendant, so conditioning
on the new roots leaves the activation of the old colliders as before.
[Proposition 1](https://proceedings.neurips.cc/paper/2019/file/c3d96fbd5b1b45096ff04c04038fff5d-Paper.pdf#page=7)

## Figure 2

[Figure2.lean](../../OpenCausalScience/Papers/KocaogluEtAl2019/Figure2.lean)
expands each dashed bidirected edge in Figure 2(a,b) into an explicit
latent root with two children. It checks the target difference `{X}`
and reproduces all 160 pairwise d-separation answers over the four
observed variables and `F_X`. Each of the two augmented graphs gives
the same answers, and `F_X` and `Y` are inseparable by observed
conditioning. The figure suppresses the isolated root corresponding
to the empty self-comparison. [Figure 2 and Theorem 2](https://proceedings.neurips.cc/paper/2019/file/c3d96fbd5b1b45096ff04c04038fff5d-Paper.pdf#page=7)

The cross-regime d-separation equivalence in Proposition 1(2), the
probability characterization in Theorem 2, and the learning algorithm
remain open in Lean. The [public CGA augmented MAG routine](https://github.com/snu-causality-lab/cga/blob/main/docs/reference/SOFT_INTERVENTION.md)
compares the projected graphs and replays the two source candidates.
The [2020 extension](jaber-et-al-2020-unknown-soft-targets.md) allows both
targets and mechanism labels to vary across candidate pairs.

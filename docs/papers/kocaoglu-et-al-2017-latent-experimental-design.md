# Kocaoglu, Shanmugam and Bareinboim (2017), experimental design with latent variables

<!-- topic: Experimental design -->

The paper models unmeasured confounders as exogenous latent roots and
learns ancestral relations among observed variables by intervening on
sets of those variables. Its independence oracle is assumed faithful to
the post-intervention distributions. [Assumptions and Lemma 1](https://papers.nips.cc/paper_files/paper/2017/file/291d43c696d8c3704cdbe0a72ade5f6c-Paper.pdf#page=4)

[AncestralRelations.lean](../../OpenCausalScience/Papers/KocaogluEtAl2017Latent/AncestralRelations.lean)
proves the graphical part of Lemma 1. After removing incoming arrows
at the intervention targets, an unconditioned active walk from a
randomized observed vertex must follow arrows downstream. Since latent
vertices are roots, the walk stays within the observed induced graph.
`randomized_dconnected_iff_observable_ancestry` gives the equivalence
between this d-connection test and post-intervention directed ancestry.
The graph theorem uses the root condition. The paper uses faithfulness
to replace the graphical test with statistical dependence.

`strongly_separating_design_recovers_ancestry` proves the graphical
closure step of Algorithm 1. Each positive test is an ancestral
relation in the original observed graph. For each original observed
arrow, a strongly separating design includes an experiment that targets
its tail and leaves its head outside the target, so the arrow survives
in at least one experiment. The final transitive closure therefore
recovers exactly the original observed ancestry. This assumes a
strongly separating design is supplied. The construction and its
intervention bound, and subsequent direct-edge and latent-confounder
recovery, remain open in Lean. [Lemma 2, Theorem 1 and Algorithm 1](https://papers.nips.cc/paper_files/paper/2017/file/291d43c696d8c3704cdbe0a72ade5f6c-Paper.pdf#page=5)

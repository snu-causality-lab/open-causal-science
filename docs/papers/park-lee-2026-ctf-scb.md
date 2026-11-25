# Park and Lee (2026), counterfactual structural causal bandits

<!-- topic: Causal decision making -->

[Paper index](../paper-checks.md)

The independent [Lean package](../../analysis/ctf-scb/README.md) checks selected
statements from *Counterfactual Structural Causal Bandits*, ICLR 2026. Its source
is the proceedings PDF with SHA-256
`4f50fd16f223ca4a5bd008c10872d81aecab6b5007a9df68eee0049a1ab6f72d`.
[Proceedings](https://proceedings.iclr.cc/paper_files/paper/2026/hash/da80970c6ca6967f2a4de6f2e13c4bae-Abstract-Conference.html)

The [proceedings checks](../../analysis/ctf-scb/MecLean/CtfScb/ICLR.lean) show
that the no-conflict test in Proposition 1 can fail for an action whose reward
is realizable. They exhibit two distinct but equivalent possibly optimal specifications under
the premise of Proposition 2. They also show that retaining a fixed-input edge in
the published regime graph can give an empty border for a dominated action,
as in Corollary 3 and Theorem 2. A further example isolates a fixed reward
input from an intervention on its source.

In the [corrected characterization](../../analysis/ctf-scb/MecLean/CtfScb/POMIS.lean),
the regime graph is the reward-ancestral subgraph after cutting the selected
fixed-input edges. `ctfPomis_iff` proves the empty-border characterization for
parent-input specifications, and `enumerating_ctfPOMIS` proves the
specification enumeration returns all and only representatives.
[`ctfPOMISs_optimal`](../../analysis/ctf-scb/MecLean/CtfScb/Border.lean) proves
optimal-value preservation. The model has finite domains and independent finite
exogenous roots. The checks cover the represented structural actions.

The structural statements and fixed-input conventions follow Sections 6.2–6.5
of the authors' later treatment. The public source chapter matches the scope
checked here. [Park and Lee, arXiv:2611.14066v1](https://arxiv.org/html/2611.14066v1)

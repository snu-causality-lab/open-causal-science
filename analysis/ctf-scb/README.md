# Counterfactual Structural Causal Bandits in Lean

This standalone package examines selected statements of Min Woo Park and Sanghack Lee,
[*Counterfactual Structural Causal Bandits*](https://proceedings.iclr.cc/paper_files/paper/2026/hash/da80970c6ca6967f2a4de6f2e13c4bae-Abstract-Conference.html),
ICLR 2026. Statement and page numbers refer to the
[proceedings PDF](https://proceedings.iclr.cc/paper_files/paper/2026/file/da80970c6ca6967f2a4de6f2e13c4bae-Paper-Conference.pdf),
SHA-256 `4f50fd16f223ca4a5bd008c10872d81aecab6b5007a9df68eee0049a1ab6f72d`.

## Proceedings statements

| Source | Checked example and scope |
| --- | --- |
| Proposition 1, p. 4 | In a five-vertex DAG, the ancestry test reports a conflict, while the counterfactual action has the same reward as an ordinary intervention on every unit. [`ICLR.N1.iclr_prop1_onlyIf_false`](MecLean/CtfScb/ICLR.lean) |
| Proposition 2 and Corollary 2, p. 7 | In a three-vertex DAG, two different specifications are possibly optimal and equivalent. The uniqueness statement holds up to equivalence under the corrected formulation. [`ICLR.C5.iclr_prop2_literal_false`](MecLean/CtfScb/ICLR.lean) |
| Corollary 3 and Theorem 2, p. 8 | In a three-vertex causal diagram, the printed regime graph retains a fixed-input edge and has empty interventional border. The action is a realizable ctf-MIS, and an ordinary intervention weakly dominates it in every conforming model. The fixed-input graph has a nonempty border. [`ICLR.C1.iclr_thm2_false`](MecLean/CtfScb/ICLR.lean) |
| Algorithms 1 and 2 and Appendix F.6, pp. 8, 28, 37 | A three-vertex example distinguishes fixing a single input of the reward mechanism, intervening on its source vertex, and omitting the fixed input. The examples establish the three outcome classifications. [`ICLR.N4.graph` and `ICLR.N4.pomis`](MecLean/CtfScb/ICLR.lean) |

## Structural results

The structural statements correspond to Sections 6.2–6.5 of Park and Lee,
[*Generalizing Causal Decision-Making*](https://arxiv.org/html/2611.14066v1),
arXiv:2611.14066v1. The source chapter's SHA-256 is
`1c4656f108ebfa3154c8873dbcf14c8fba46f89034de88847094f98ae96d9156`.
The ctf-MIS and ctf-POMIS statements are Theorems 81 and 87, and the
specification enumerator corresponds to Algorithm 11.

The model has finite domains and independent finite exogenous roots. A conforming
model has exactly the specified directed and bidirected diagram, and its
mechanisms may ignore listed inputs. The reward is a real-valued function of
the outcome. A parent-input specification selects directed edges and supplies
a constant separately at each receiving argument. An outer-target action
computes its targets in a fixed-input system and substitutes those values into
the natural system. The unnested specialization represents coherent shared
computations using one parent-input specification.

| Result | Lean declarations |
| --- | --- |
| Counterfactual actions can match or improve the best ordinary interventional reward | [`l2_dominance`](MecLean/CtfScb/MIS.lean) |
| The minimality characterization with two graphical conditions | [`ctfMIS_iff`](MecLean/CtfScb/MIS.lean), [`ctfMIS_iff_unnested`](MecLean/CtfScb/Unnested.lean) |
| A reduction from a realizable outer-target action to a minimal one with unchanged reward | [`cor_ctf_misify`](MecLean/CtfScb/Misify.lean) |
| Possible optimality iff the corrected regime graph's border is empty | [`ctfPomis_iff`](MecLean/CtfScb/POMIS.lean) |
| Corrected enumeration returns all and only ctf-POMIS representatives | [`enumerating_ctfPOMIS`](MecLean/CtfScb/POMIS.lean), [`ctfPOMISs_not_equiv`](MecLean/CtfScb/Border.lean) |
| The representatives preserve the best optimized reward | [`ctfPOMISs_optimal`](MecLean/CtfScb/Border.lean) |

The corrected regime graph deletes fixed-input edges and restricts to the
remaining ancestors of the reward. It retains the reward mechanism even
when some of its inputs are fixed. The enumeration theorem concerns the
Lean specification enumerator using these rules. General nested term syntax,
complexity bounds, implementations of online learning, and empirical regret
results are outside this package's scope.

## Check the proofs

From this directory, run the following commands with Elan installed. The
toolchain and Mathlib are pinned to Lean 4.36.0 and Mathlib 4.36.0.

```sh
lake exe cache get
lake build
lake env lean MecLean/AxiomCheck.lean
```

The axiom check lists the transitive dependencies of the reported declarations.
The expected dependencies are Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`.

Fourteen supporting modules are copied from the public
[Lee and Bareinboim 2018 formalization](https://github.com/sanghack81/SCMMAB-NIPS2018/tree/49b6c9f285135afafe533913c07c25f8e4db54bc/lean).
Their MIT notice is included in [LICENSE.LB2018.txt](LICENSE.LB2018.txt).

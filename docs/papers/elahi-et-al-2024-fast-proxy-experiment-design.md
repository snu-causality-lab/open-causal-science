# Elahi, Akbari, Etesami, Kiyavash and Thiran (2024), fast proxy experiment design

<!-- topic: Experimental design -->

[Paper index](../paper-checks.md)

> **Verified counterexample** · [Lemma 2 and Algorithm 1, line 8](#the-intervention-domain) · The printed split network can select the outcome itself, even when the resulting experiment cannot identify its response to treatment.

> **Verified counterexample** · [Lemma 2, eligibility of adjustment variables](#a-treatment-descendant-in-the-adjustment-set) · A zero-cost observational cut can adjust for a treatment descendant and give the wrong response, even with interventions restricted to vertices outside the target ancestor set.

[NeurIPS 2024, §4 and Appendix C.2](https://papers.nips.cc/paper/2024/file/5bd9fbb3a5a985f80c16ddd0ec1dfc43-Paper-Conference.pdf) extends the experimental design question of [Akbari et al.](akbari-et-al-2025-optimal-experiment-design.md).
For the §4 query, let `S` be the ancestors of the outcomes after deleting the treatment vertices from the graph. The treatment is taken to be minimal for Rule 3, giving `Pa(S) = X` in the proof of Lemma 2. In Figure 2(a) and the two-vertex example below this identity follows directly from the arrows.

## Split copies and moral cuts

[SplitNetwork.lean](../../OpenCausalScience/Papers/ElahiEtAl2024/SplitNetwork.lean) starts with the expanded directed graph after removing the outgoing arrows of `Pa(S)` and replacing each bidirected edge by a latent parent of its two endpoints. Its reachability theorem applies to any directed edge relation on this expanded vertex type.

A first copy denotes its original vertex. Its removal is an adjustment choice. Removing a second copy disables incoming arrows for that vertex. Every moral edge lifts to two edges through an available second copy, and every two-edge passage between first copies projects to either a moral edge or equality. `split_route_iff_moral_route` proves both directions for arbitrary walks. `split_cut_iff_moral_cut` transfers the terminal cut property. `minimum_split_cut_iff_minimum_moral_cut` transfers minimum cost among eligible choices when the first copies are free and the cost depends on the second copies.

The causal use of the construction protects both copies of any latent root, both sets of first-copy terminals, and the second copies of `S`. Eligible adjustments also have to satisfy the ancestry condition of Lemma 2. The Lean cost theorem is a graph equivalence for supplied eligibility and costs. It does not verify the numerical solver, the treatment preprocessing, or necessity of the graphical criterion among all identifying functionals. [Algorithm 1 and Theorem 3](https://papers.nips.cc/paper/2024/file/5bd9fbb3a5a985f80c16ddd0ec1dfc43-Paper-Conference.pdf#page=8)

## Figure 2(a)

On the graph in [Figure 2(a)](https://papers.nips.cc/paper/2024/file/5bd9fbb3a5a985f80c16ddd0ec1dfc43-Paper-Conference.pdf#page=2), the treatment is `{v₂,v₃}`, the outcome is `y`, and `S={w,y}`. [Figure2A.lean](../../OpenCausalScience/Papers/ElahiEtAl2024/Figure2A.lean) verifies that intervening on `v₁` gives a cut with no adjustment. Without an intervention, the path `v₂ – U₁₂ – U₁w – w` remains in the expanded moral graph. Here `U₁₂` and `U₁w` are the distinct latent roots of the bidirected edges. They are joined by moralizing their shared child `v₁`. Consequently the path survives every eligible adjustment set, whether it contains `v₁` or is empty. With both treatments unavailable and `S` protected, `v₁` is the only admissible intervention.

## The intervention domain

[OutcomeIntervention.lean](../../OpenCausalScience/Papers/ElahiEtAl2024/OutcomeIntervention.lean) uses the ADMG with `X → Y` and `X ↔ Y`, so the treatment is `X` and `S={Y}`. Algorithm 1 line 8 assigns reported costs to every observed second copy. With `C(X)=2` and `C(Y)=1`, the printed network has a unique cheapest cut at the second copy of `Y`. The adjustment set is empty. The proof of Lemma 2 uses Eq. (6) for `W=I∪Pa(S)` even though a set `W` containing `Pa(S)` can still intersect `S`.

[ExternalIntervention.lean](../../OpenCausalScience/Papers/ElahiEtAl2024/ExternalIntervention.lean) proves the equality used in Eq. (6) for ranked binary structural models with explicit latent variables and a shared finite rational exogenous law. The original regime clamps all directed external parents of `S`. The larger regime preserves those values and leaves `S` free. The theorem proves equality unit by unit and then for every event on `S`. The proof makes no independence assumption on the exogenous coordinates.

The Lean counterexample has two binary causal models with a fair common cause. Both models have strictly positive treatment and outcome mechanisms, both have non-redundant treatment, and they agree on the full observational law and every assignment of the `do(Y)` law. Their probabilities of `Y=1` under `do(X=1)` are `5/8` and `9/16`. Thus the cheaper experiment does not identify the response, even with observational data. When the second copy of `Y` is protected, the cut requires intervention on `X`. More generally, protecting the second copies of `S` imposes `I∩S=∅` in the §4 cut search and addresses this failure of the printed conditions. Proposition 2 already imposes this disjointness in its single-district optimization. [Lemma 2 and Algorithm 1](https://papers.nips.cc/paper/2024/file/5bd9fbb3a5a985f80c16ddd0ec1dfc43-Paper-Conference.pdf#page=8) · [Appendix C.2, Eq. (6)](https://papers.nips.cc/paper/2024/file/5bd9fbb3a5a985f80c16ddd0ec1dfc43-Paper-Conference.pdf#page=21) · [Proposition 2](https://papers.nips.cc/paper/2024/file/5bd9fbb3a5a985f80c16ddd0ec1dfc43-Paper-Conference.pdf#page=4)

## A treatment descendant in the adjustment set

[DescendantAdjustment.lean](../../OpenCausalScience/Papers/ElahiEtAl2024/DescendantAdjustment.lean) considers the chain `X₁ → Y₁ → Z → X₂ → Y₂` and the joint response of `{Y₁,Y₂}` to `{X₁,X₂}`. Both treatments are necessary. After deleting the treatment vertices, the outcome ancestor set is `S={Y₁,Y₂}` and its external parents are `{X₁,X₂}`. Lemma 2 requires adjustment vertices to belong to `Anc(S)` and separate `S` from `Pa(S)` after the prescribed edge deletions and moralization. In the original graph `Z` is an ancestor of `Y₂` through `X₂` and a descendant of `X₁` through `Y₁`. For `I=∅`, the only arrows deleted are those leaving the treatments. This leaves the moral path `Y₁ – Z – X₂`, so removing `Z` separates the two terminal sets. The proof of Lemma 2 uses the claim that the adjustment set contains no descendants of `Pa(S)`, which fails in this graph. [Lemma 2](https://papers.nips.cc/paper/2024/file/5bd9fbb3a5a985f80c16ddd0ec1dfc43-Paper-Conference.pdf#page=8) · [Proof in Appendix C.2](https://papers.nips.cc/paper/2024/file/5bd9fbb3a5a985f80c16ddd0ec1dfc43-Paper-Conference.pdf#page=21)

Take `X₁` to be a fair bit and let each child copy its parent with probability `3/4` under the observational factorization. At `X₁=X₂=1`, the conditional probabilities of `Y₁=1` are `9/10` for `Z=1` and `1/2` for `Z=0`. Both values of `Z` have observational probability `1/2`. The module proves positivity and checks that the adjustment formula gives `7/10` for the margin `Y₁=1`, while the interventional probability is `3/4`. Requiring adjustment vertices to lie outside the directed descendants of `Pa(S)` in the original graph rules out this cut. [Adjustment formula in Appendix C.2](https://papers.nips.cc/paper/2024/file/5bd9fbb3a5a985f80c16ddd0ec1dfc43-Paper-Conference.pdf#page=21)

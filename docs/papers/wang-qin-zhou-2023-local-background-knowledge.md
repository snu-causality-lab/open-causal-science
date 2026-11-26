# Wang, Qin and Zhou (2023), local background knowledge

<!-- topic: Discovery -->

Tian-Zuo Wang, Tian Qin and Zhi-Hua Zhou, *Sound and complete causal identification with latent variables given local background knowledge*, Artificial Intelligence 322 (2023), 103964. The check uses Algorithm 1 and Theorem 1, pp. 4–5, and the path and invariance arguments in Appendix B, pp. 17–19 of the journal article. [Journal article](https://doi.org/10.1016/j.artint.2023.103964)

## Minimal possibly directed paths

Lemma 2 shortens a possibly directed path until it has no chord. The Lean proof chooses a chord of minimum span and rules out an arrowhead pointing backward along it. For a triangle it uses the first Balanced clause, closure under R2, and ancestrality. For a longer chord it uses closure under R1 to propagate directed edges along the unshielded triples, and the no-selection orientation of an edge with a tail. A backward arrowhead would then contradict ancestrality. The shorter path keeps both endpoints and uses only vertices of the input path, so any vertex avoidance property carries over.

| Statement | Lean declaration |
| --- | --- |
| The shortest chord on a possibly directed path is possibly directed forward. | `PMG.isolated_chord_points_possibly_forward` |
| A possibly directed path has a chordless possibly directed path with the same endpoints and no new vertices. | `PMG.exists_uncovered_possible_path` |
| An agreeing ancestral graph gives the ancestry constraint used in the shortcut proof. | `PMG.no_arrowhead_into_ancestor_of_agreeing_graph` |

## Arrowheads into a circle component

The first clause of Theorem 1's Balanced property says that `A *→ B o-* C` implies `A *→ C`. Lemma 3 extends this property from one edge to a circle component. Starting at `B`, propagate the head into each successive vertex along a circle–circle walk. If the walk returned to `A`, the previous vertex would have both a head and a circle on the same adjacency to `A`.

| Statement | Lean declaration |
| --- | --- |
| An arrowhead into one vertex of a circle component propagates to every vertex in that component. | `PMG.arrowhead_into_circle_component` |
| The source of the arrowhead belongs to a different circle component. | `PMG.source_outside_circle_component` |

The declarations quantify over finite partially marked graphs and state the relevant properties of the input explicitly. [Lean source](../../OpenCausalScience/Papers/WangQinZhou2023/LocalBackgroundKnowledge.lean)

## Local updates and descendant sets

The local knowledge fixes all circle endpoints at one vertex. The Lean statements take a compatible no-selection MAG and the tail-witness direction of the preceding PMG's Complete property. Every asserted direction applies to an arbitrary compatible MAG. A witness for an old circle may belong to the preceding class without meeting the new local knowledge.

| Source | Lean declaration | Statement checked |
| --- | --- | --- |
| R11 | `r11_sound` | A definite tail forces an arrowhead at the other endpoint under no selection. |
| Lemma 4 | `possible_descendants_eq_descendants` | The possible descendants after removing the selected vertices are the descendants in each compatible MAG. |
| Lemma 7, Step 1 | `step1_directs_unselected_edge`, `step1_head_at_descendant` | An unselected circle at the treatment points out, and every selected vertex adjacent to a descendant has a head at the descendant. |
| Lemma 7, Step 2 | `step2_from_different_f`, `step2_propagates_direction` | The strict difference of the two `F` sets and the unshielded propagation case both force the direction in the compatible class. |
| Lemmas 9–11 | `selected_vertices_are_adjacent`, `descendant_cannot_be_parent_of_selected`, `no_opposing_demands` | The selected vertices form a clique, their parents exclude the possible descendants, and directions established in a compatible MAG cannot conflict. |

These results give the invariance arguments for Steps 1 and 2 and explain why the same Step 2 edge cannot receive opposite demands when the knowledge is correct. [Lean source](../../OpenCausalScience/Papers/WangQinZhou2023/LocalTransformation.lean)

## Modified discriminating-path rule

Proposition 1 replaces FCI's R4 with R′4 for local background knowledge. `exists_minimal_collider_subpath` proves that any collider path contains a minimal collider subsequence with the same endpoints. `r4_prime_sound` proves R′4 given the initial PAG's definite arrowheads on minimal collider paths, using the implication from [Zhao, Zheng and Liu's Theorem 2.1](https://files.sciengine.com/pdfs/1006-9283/RwHHFBSrAywG9iMad.pdf) and initial PAG completeness as an explicit premise. If the final edge were bidirected, every earlier possible predecessor of its endpoint would have a tail pointing to that endpoint. The minimal collider subsequence must therefore still contain the discriminated vertex as its last interior collider, forcing a head where the current graph has a circle. [Lean source](../../OpenCausalScience/Papers/WangQinZhou2023/DiscriminatingRule.lean)

Establishing the full output of Theorem 1 still requires correspondence with Algorithm 1's saturation and propagation, and proof that its updated PMG satisfies Chordal, Balanced and Complete. In particular, the MAG constructions in Lemmas 16.1 and 16.2 remain separate.

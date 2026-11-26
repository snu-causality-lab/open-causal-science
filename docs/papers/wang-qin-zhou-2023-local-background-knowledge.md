# Wang, Qin and Zhou (2023), local background knowledge

<!-- topic: Discovery -->

Tian-Zuo Wang, Tian Qin and Zhi-Hua Zhou, *Sound and complete causal identification with latent variables given local background knowledge*, Artificial Intelligence 322 (2023), 103964. The check uses Theorem 1, p. 5, and Lemmas 2 and 3, p. 17 of the journal article. [Journal article](https://doi.org/10.1016/j.artint.2023.103964)

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

The declarations quantify over finite partially marked graphs and state the relevant properties of the input explicitly. They cover Lemmas 2 and 3 from those properties. Algorithm 1's establishment of those properties and the validity criterion for local transformations remain outside this check. [Lean source](../../OpenCausalScience/Papers/WangQinZhou2023/LocalBackgroundKnowledge.lean)

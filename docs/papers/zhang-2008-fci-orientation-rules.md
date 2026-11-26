# Zhang (2008), FCI orientation rules

<!-- topic: Discovery -->

Jiji Zhang, *On the completeness of orientation rules for causal discovery in the presence of latent confounders and selection bias*, Artificial Intelligence 172 (2008), 1873–1896. The check uses the FCI rules in §3, pp. 1879–1880 and the augmented rules and Theorem 1 in §4, pp. 1880–1882. [Journal article](https://doi.org/10.1016/j.artint.2008.08.001)

## Soundness of the individual orientation rules

The theorems quantify over finite ancestral graphs and allow undirected edges. Each mark conclusion is stated for a compatible fully marked graph, with the fixed marks and the relevant noncollider or discriminating-path information as hypotheses.

| Rule | Lean declaration | Statement checked |
| --- | --- | --- |
| R0 | `r0_collider_iff_outside_separator` | An unshielded triple is a collider exactly when its middle vertex lies outside a separating set of its endpoints. |
| R1 | `r1_sound` | In an unshielded triple `A *→ B o-* C` with a noncollider witness in the equivalence class, every matching MAG with the head at `B` on `AB` has `B → C`. |
| R2 | `r2_sound` | From `A → B *→ C` or `A *→ B → C`, any `A–C` adjacency has an arrowhead at `C`. |
| R3 | `r3_sound` | For the R3 configuration, the noncollider at `D` forces the head at `B` on `BD`. |
| R4 | `collider_iff_outside_separator`, `r4_sound` | A separating set of the discriminating path endpoints determines the middle mark in the final triple. The proof verifies both the directed and bidirected branches. |
| R5 | `r5_sound` | Every edge on the uncovered circle cycle is undirected, using the noncollider status of its consecutive triples. |
| R6 | `r6_sound` | An undirected edge forces a tail on another edge at their shared vertex. |
| R7 | `r7_sound` | A tail at the first vertex of an unshielded noncollider forces a tail at the middle vertex on its second edge. |
| R8 | `r8_sound` | From `A → B → C` or `A -o B → C`, a partially oriented `A o→ C` must be `A → C`. |
| R9 | `r9_sound` | The uncovered potentially directed path and the noncollider at its start force the directed shortcut. |
| R10 | `r10_sound` | The two uncovered potentially directed paths and their unshielded noncollider at the common start force the directed shortcut. |

The unshielded rules use unshielded-collider invariance to transfer R0 information across the equivalence class. R4 proves the separator property from m-separation. [Unshielded-collider invariance](ali-richardson-spirtes-2009-mag-equivalence.md) · [Edge rules](../../OpenCausalScience/Papers/Zhang2008OrientationRules/Orientations.lean) · [Unshielded paths](../../OpenCausalScience/Papers/Zhang2008OrientationRules/UnshieldedPaths.lean) · [Discriminating paths](../../OpenCausalScience/Papers/Zhang2008OrientationRules/DiscriminatingPaths.lean)

## Chordality of the remaining circle graph

The proof follows the chordality argument in Lemma 3 of Zhang's UAI 2007 paper, a precursor to the 2008 article. It permits undirected edges and tail–circle edges. P1 excludes arrowheads on adjacencies within a circle component, the tail–circle propagation clause of P3 excludes tail–circle edges there, and R6 excludes undirected edges that meet a circle endpoint. Consequently, a cycle with no circle chord has no skeleton chord and would still trigger R5. [UAI paper](https://arxiv.org/abs/1206.5282)

| Lean declaration | Statement checked |
| --- | --- |
| `CircleStructure.tail_circle_source_outside` | A tail–circle edge has endpoints in different circle components under the stated P3 clause. |
| `CircleStructure.adjacent_in_circle_component` | An adjacency within a circle component is a circle edge under P1, the P3 clause, and R6 closure. |
| `CircleStructure.chordal_of_r5_closed` | R5 closure then makes the remaining circle graph chordal. |

The proof takes the named structural and closure properties as hypotheses. The full FCI proof also requires correctness of skeleton and separator discovery, the derivation of the structural properties, and the completion arguments that show each remaining circle can vary among compatible MAGs. [Lean source](../../OpenCausalScience/Papers/Zhang2008OrientationRules/CircleStructure.lean)

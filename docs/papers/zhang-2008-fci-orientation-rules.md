# Zhang (2008), FCI orientation rules

<!-- topic: Discovery -->

Jiji Zhang, *On the completeness of orientation rules for causal discovery in the presence of latent confounders and selection bias*, Artificial Intelligence 172 (2008), 1873–1896. The check uses the FCI rules in §3, p. 1879 and the R8 soundness case of Theorem 1, p. 1881. [Journal article](https://doi.org/10.1016/j.artint.2008.08.001)

## Soundness of R1, R2 and R8

The theorems concern one orientation at a time and quantify over finite ancestral graphs. They allow undirected edges and use the ancestral restrictions on arrowheads at undirected vertices and at ancestors.

| Rule | Lean declaration | Statement checked |
| --- | --- | --- |
| R1 | `r1_sound` | In an unshielded triple `A *→ B o-* C` with a noncollider witness in the equivalence class, every matching MAG with the head at `B` on `AB` has `B → C`. |
| R2 | `r2_sound` | From `A → B *→ C` or `A *→ B → C`, any `A–C` adjacency has an arrowhead at `C`. |
| R8 | `r8_sound` | From `A → B → C` or `A -o B → C`, a partially oriented `A o→ C` must be `A → C`. |

R1 reuses the [proof of unshielded-collider invariance](ali-richardson-spirtes-2009-mag-equivalence.md). Its noncollider witness supplies the information established by the earlier R0 step. R2 and R8 follow from the marked-edge restrictions in each compatible graph. The complete FCI procedure and the completeness of the orientation rules in combination are separate results. [Lean source](../../OpenCausalScience/Papers/Zhang2008OrientationRules/Orientations.lean)

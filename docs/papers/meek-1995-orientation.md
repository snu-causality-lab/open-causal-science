# Meek (1995), orientation rules and consistent extensions

<!-- topic: Discovery -->

Meek uses orientation rules to find the arrows shared by DAG extensions of a pattern, including extensions consistent with background knowledge. The formalization keeps the original skeleton and unshielded-collider signature explicit, so a background orientation restricts the same extension set. [UAI paper, Figure 1 and Theorems 2–4](https://arxiv.org/abs/1302.4972) · [CGA's PDAG and Meek rules](https://github.com/snu-causality-lab/cga/blob/v0.2.0a1/docs/reference/GRAPH_OPERATIONS.md#pdags-meek-rules-and-background-knowledge)

## Soundness and termination

[Closure.lean](../../OpenCausalScience/Papers/Meek1995/Closure.lean) proves that every R1–R4 proposal is forced in each consistent extension, provided the original unshielded colliders are oriented in the input. R1 uses the absence of a new collider and R2 uses acyclicity. The proofs for R3 and R4 combine those two effects. The R4 implication also applies without requiring the dashed adjacency in the published diagram, matching the antecedent used by CGA.

A simultaneous round preserves the entire extension set. Every changing round adds an arrow, so the iteration reaches a stationary round within the number of ordered vertex pairs. The declarations describe the mathematical rules and their iterations.

## Maximal orientation and chordality

For a complete skeleton, [CompleteSkeleton.lean](../../OpenCausalScience/Papers/Meek1995/CompleteSkeleton.lean) proves that any edge left open after closure has a consistent extension in each direction, including when the starting orientation incorporates background knowledge. The order constraints on a clique are transitive at an R2 fixed point. Either unresolved preference extends to a total ordering, which orients the complete skeleton.

[ChordlessCycle.lean](../../OpenCausalScience/Papers/Meek1995/ChordlessCycle.lean) checks the argument of Lemma 2. In any acyclic orientation of an induced cycle, both cycle edges point into a vertex with maximum rank. The two cycle neighbors are nonadjacent and give an unshielded collider. The general closure completeness proof in Theorems 3 and 4 also uses the structure and compatible orientations of chordal components.

[JoinTreeOrientation.lean](../../OpenCausalScience/Papers/Meek1995/JoinTreeOrientation.lean) formalizes the rooted join-tree construction used in Lemmas 4–5. Bags containing a vertex satisfy running intersection. Ordering vertices by the depth of their first bag makes the earlier neighbors of each vertex appear in its own first bag, so no unshielded collider is introduced. A chosen clique in the root bag can be placed first in a prescribed order.

[ChainComponents.lean](../../OpenCausalScience/Papers/Meek1995/ChainComponents.lean) shows that R1 saturation propagates a fixed parent along an undirected component, given a topological order of the components. It also shows that a collider-free orientation of one component can replace that component in a consistent extension. In this structured setting an open edge has extensions in both directions when a root bag contains its endpoints. Deriving the ordered component structure from arbitrary R1–R3 closure, and orienting chordal components with internal background constraints, remain separate steps.

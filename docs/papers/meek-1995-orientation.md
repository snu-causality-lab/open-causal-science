# Meek (1995), orientation rules R1 and R2

<!-- topic: Discovery -->

Meek uses orientation rules to find the arrows shared by DAG extensions of a pattern, including extensions consistent with background knowledge. This companion records two individual rules used in CGA's orientation procedure. [UAI paper](https://arxiv.org/abs/1302.4972) · [CGA's PDAG and Meek rules](https://github.com/snu-causality-lab/cga/blob/v0.2.0a1/docs/reference/GRAPH_OPERATIONS.md#pdags-meek-rules-and-background-knowledge)

[Orientation.lean](../../OpenCausalScience/Papers/Meek1995/Orientation.lean) works in an arbitrary finite DAG extension. For R1, if the extension preserves the absence of an unshielded collider, an incoming arrow at the middle vertex forces the other adjacent edge to point out. For R2, an adjacency between the endpoints of a directed path must follow the path's direction by acyclicity. The path result includes the two-arrow premise used in R2.

These are soundness statements for individual orientations. Meek's closure completeness with and without background knowledge is a separate result.

# Lauritzen and Wermuth (1989), graphical association models

<!-- topic: Graphical Markov models -->

Steffen L. Lauritzen and Nanny Wermuth, *Graphical Models for Associations between Variables, Some of Which Are Qualitative and Some Quantitative*, Annals of Statistics 17(1), 31–57. The paper studies recursive graphical models whose variables can include both categorical and continuous measurements. Directed arrows order blocks and undirected lines represent within-block associations. [Published article](https://doi.org/10.1214/aos/1176347003)

[ChainGraph.lean](../../OpenCausalScience/Graph/ChainGraph.lean) represents finite chain graphs with a rank constant on each line component and strictly increasing along arrows. `component_eq_true_iff` connects the executable component test with undirected reachability. `component_arrow_increases` and `no_semidirected_return` establish the component ordering and the exclusion of semidirected cycles in this representation. `ofDAG_component_singleton` specializes to singleton components for every finite DAG.

[ChainMarkov.lean](../../OpenCausalScience/Graph/ChainMarkov.lean) uses the later [Drton C1–C3 formulation](drton-2009-discrete-chain-graph-models.md) for the LWF block-recursive property. The binary reference check is exact on rational contingency tables. The general implications between the paper's mixed discrete–continuous density factorization, the block-recursive implications and the [LWF global Markov property](frydenberg-1990-chain-graph-markov.md) remain open in Lean.

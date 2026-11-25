# Kivva et al. (2022), Example 2

<!-- topic: Identification -->
<!-- index-anchor: kivva-et-al-2022-example-2 -->

[Paper index](../paper-checks.md)

The [proceedings PDF, pp. 4–5](https://proceedings.mlr.press/v180/kivva22a/kivva22a.pdf) has SHA-256 `8e677c27d3f725e404b97123b7068e16ebf6f7c9be067241e41e0ac3763bb2ea`. [Example2.lean](../../OpenCausalScience/Papers/KivvaEtAl2022/Example2.lean) encodes the two displayed binary kernels. At `do(X₁=0, X₂=1)` it finds `P(Y₁=0, Y₂=0)` equal to `2/9` and `5/18` when averaging the two equally weighted values of `U₂`. The printed values `4/9` and `5/9` are twice these probabilities. The outcomes still differ. The observational laws agree and give zero weight to off-diagonal treatment assignments, placing the example outside the positive model class of Definition 5.

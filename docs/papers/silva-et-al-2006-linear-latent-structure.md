# Silva, Scheines, Glymour and Spirtes (2006), linear latent structure

<!-- topic: Linear graphical models -->

[Original paper, §3 and the BuildPureClusters procedure](https://www.jmlr.org/papers/v7/silva06a.html)

The [Lean companion](../../OpenCausalScience/Papers/SilvaEtAl2006/OneFactorTetrads.lean)
checks the covariance equations of a single-factor linear measurement model.
The latent factor is uncorrelated with the measurement errors. When the four
cross-error covariances vanish, `cross_tetrad_eq_zero` proves the corresponding
tetrad equality for any rational loadings and factor variance.
`all_three_tetrads_vanish` checks all three equalities for four distinct
indicators with uncorrelated measurement errors.

The general graphical interpretation of tetrads and the clustering guarantee
for BuildPureClusters remain open here.

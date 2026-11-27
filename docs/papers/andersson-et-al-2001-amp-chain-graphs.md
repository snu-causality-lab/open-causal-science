# Andersson, Madigan and Perlman (2001), alternative Markov properties for chain graphs

<!-- topic: Graphical Markov models -->

Steen A. Andersson, David Madigan and Michael D. Perlman, *Alternative Markov Properties for Chain Graphs*, Scandinavian Journal of Statistics 28(1), 33–85. The paper gives the AMP interpretation of a chain graph and relates it to block-recursive Gaussian models. The corresponding LWF and AMP constraints can differ even on the three-vertex flag `A → B — C`. [Journal article](https://doi.org/10.1111/1467-9469.00224) · [UAI 1996 precursor, p. 46 and Theorem 4.2](https://arxiv.org/pdf/1302.3553#page=7)

[Flag.lean](../../OpenCausalScience/Papers/AnderssonEtAl2001/Flag.lean) constructs two strictly positive normalized rational distributions for the flag. In `lwfLaw`, each of the two successive bits is a noisy copy of the preceding bit, yielding `A ⟂ C | B`. In `ampLaw`, the endpoint bits are independent and the middle bit is their noisy parity, yielding `A ⟂ C`. `lwf_holds_amp_fails` and `amp_holds_lwf_fails` check membership and nonmembership against all the applicable [block-recursive conditions](drton-2009-discrete-chain-graph-models.md). The two distributions are constructed for this check.

The [p-separation companion](levitz-et-al-2001-amp-p-separation.md) identifies the activation rule behind the flag example. The general no-nonimmorality-flag characterization, AMP graph equivalence criterion, augmentation equivalence and Gaussian representation remain open in Lean.

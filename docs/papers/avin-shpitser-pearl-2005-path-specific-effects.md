# Avin, Shpitser and Pearl (2005), recanting witness

<!-- topic: Path-specific effects -->

[Paper index](../paper-checks.md)

Figure 5(a) has directed edges `Z → R`, `R → V`, `R → Y`, and
`V → Y`. The path through `V` takes the active `Z` value, while
the direct continuation `R → Y` takes the baseline `Z` value.
The two inputs to `Y` therefore use different responses of `R`
from the same unit. Lemma 2 uses Table 1 to vary their joint
law while keeping the separate interventional laws fixed.
[IJCAI 2005, Table 1, Figure 5 and Theorem 3](https://ijcai.org/proceedings/2005/100)

## The two models in Figure 5(a)

[Kite.lean](../../OpenCausalScience/Papers/AvinEtAl2005/Kite.lean)
keeps the two response tables from Table 1. It gives `V` a private
flip with probability `1/4` and encodes `Y` as a pair of bits, one
from each parent with its own private flip of the same probability.
These shared downstream mechanisms instantiate the construction in
Theorem 3. The primitive roots are independent.

- `regime_factorization` checks the product expression against a
  Cartesian sum over the primitive roots. `figure5a_nonidentification`
  proves equality of every cell under every perfect node intervention,
  including the observational regime. `observational_cells_positive`
  checks full observational support in both models.
- `path_formula_matches_structural_response` checks the path-specific
  mixture against direct evaluation at the same primitive noise in
  both copies of `R`. For baseline `0` and active value `1`, the
  probability of `Y = (1,1)` is `23/96` in the first model and `9/32`
  in the second.

Theorems 4–5 use the recanting-witness criterion to characterize
experimental identification in Markovian models. The Lean companion
checks the two-model construction in Theorem 3. The [recanting
district companion](shpitser-2013-longitudinal-mediation.md) covers the
graphical criterion for the later extension with hidden confounding.
[IJCAI 2005, Theorems 4–5](https://ftp.cs.ucla.edu/pub/stat_ser/r321-ijcai05.pdf#page=6)

# Shpitser and Pearl (2006), conditional interventional identification

<!-- topic: Identification -->

[Paper index](../paper-checks.md)

## Figure 3 and the soundness of an exchange

Figure 3 moves an observed variable from the conditioning set to the
intervention when Rule 2 applies. With no further exchange, the algorithm
calls ID for the reduced joint and divides by its sum over outcome values.
Theorem 7 proves soundness of the two steps. [UAI 2006 proceedings, Figure 3 and Theorem 7](https://ftp.cs.ucla.edu/pub/stat_ser/r329-uai.pdf#page=5)

[ExchangeAndNormalize.lean](../../OpenCausalScience/Papers/ShpitserPearl2006Conditional/ExchangeAndNormalize.lean)
checks one exchange followed by normalization in the finite rational
[Rule 2 response model](pearl-1995-do-calculus.md). The prior interventions
are already applied. The joint cells in the exchanged regime and the
cellwise independence used by Rule 2 are premises.

- `action_evidence_positive_of_observational_evidence` proves that
  positive observational evidence implies positive evidence in the
  exchanged regime. The former event is a subevent of the latter after
  matching the observed and assigned value of the exchanged variable.
- `joint_sum_eq_evidence_mass` shows that summing reduced joint cells
  over a duplicate-free exhaustive list of outcome values gives the
  exchanged-regime evidence mass.
- `single_exchange_then_normalize` proves the denominator is positive
  and that the resulting quotient equals the original conditional cell.

Choosing all applicable exchanges, deriving Rule 2's premises in a
general latent-variable model, and IDC completeness require further
results.

## Published correction and later hedge criterion

Shpitser's May 2007 UCLA Appendum withdraws §6 Lemma 3's claim that
Tian's `cond-identify` is unsound. It attributes the claim to a notation
misunderstanding and presents a completeness proof. Its Theorem 1 proof
uses the back-door hedge criterion, so that dependency merits rechecking
against the exact-query result before claiming a full validation of the
Appendum's proof. [UCLA R-329-APPENDUM](https://ftp.cs.ucla.edu/pub/stat_ser/r329-appendum.pdf)

UAI Corollary 2 invokes the earlier arbitrary-subquery hedge condition.
The UAI definitions allow the conditioning set to be empty. In that
case the corollary reduces to the arbitrary-subquery test refuted by the
2023 example. This conclusion comes from comparing the two statements.
[UAI 2006 proceedings, definition and Corollary 2](https://ftp.cs.ucla.edu/pub/stat_ser/r329-uai.pdf),
[Shpitser (2023), §3 and Proposition 1](https://arxiv.org/pdf/2307.03750v1#page=7)

The [joint ID record](shpitser-pearl-2006-joint-id.md#the-hedge-criterion)
links the correction to the original AAAI Corollary 3. The 2008 JMLR
article gives a later presentation of IDC in Figure 7 and Theorems 20–22.
The same article's Theorem 19 gives the earlier arbitrary-subquery test.
[JMLR 9, Theorem 19 and the IDC presentation](https://www.jmlr.org/papers/volume9/shpitser08a/shpitser08a.pdf#page=13)

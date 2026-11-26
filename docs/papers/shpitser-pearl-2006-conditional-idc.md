# Shpitser and Pearl (2006), conditional interventional identification

<!-- topic: Identification -->

[Paper index](../paper-checks.md)

> **Author correction** · [UAI §6, Lemma 3](#figure-1c-and-the-2007-appendum) · The 2007 Appendum withdraws the claim that Tian’s conditional identification procedure is unsound.

> **Verified counterexample** · [UAI Corollary 2 with empty conditioning](#later-hedge-criterion) · With empty conditioning, the corollary inherits the refuted arbitrary-subquery hedge condition.

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

The [Tian companion](tian-2004-conditional-effects.md#failure-agreement-with-idc)
checks the graph-level result of exhausting all Rule 2 exchanges.

## Figure 1(c) and the 2007 Appendum

Shpitser's May 2007 UCLA Appendum withdraws §6 Lemma 3's claim that
Tian's `cond-identify` is unsound. It attributes the claim to a notation
misunderstanding and presents a completeness proof using the back-door
hedge criterion. [UCLA R-329-APPENDUM](https://ftp.cs.ucla.edu/pub/stat_ser/r329-appendum.pdf)

[Figure1C.lean](../../OpenCausalScience/Papers/ShpitserPearl2006Conditional/Figure1C.lean)
replays the two algorithms on the graph with `X → Z`, `X ↔ Z`,
`W → Y`, and `Y → Z`. In the disputed query `Pₓ(w | z)`, the failed
district `{Z}` uses `Y`, the sole summed variable. Tian's `Pa({Y})`
includes `Y` itself, so Phase 3 pulls in `{Y}`. That factor also uses
`W`, making Phase 4 return `FAIL`. For the companion query `Pₓ(y | z)`,
the failed factor on `{Z}` already uses the outcome `Y`.
IDC cannot exchange `Z` in either query. Joint ID returns failure on
the induced pair `{X,Z}` and `{Z}` in both cases. [UAI 2006, Figure 1(c) and §6 Lemma 3](https://ftp.cs.ucla.edu/pub/stat_ser/r329-uai.pdf) ·
[Tian (2004), Figure 3](https://arxiv.org/pdf/1207.4161#page=7)

## Later hedge criterion

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

# Tian (2004), identification of conditional causal effects

<!-- topic: Identification -->

[Paper index](../paper-checks.md)

Figure 3 starts from the ancestors of outcome and evidence in the graph
with treatments removed. It runs `Identify` on each district of that
ancestral graph. Phase 3 starts with the failed district factors and
repeatedly pulls in factors that share a summed argument. Phase 4
returns `FAIL` if any outcome appears in the resulting factors' arguments.
Tian's `Pa(S)` includes the members of `S` as well as their directed
parents. [UAI 2004, §3 definition of `Pa(S)`](https://arxiv.org/pdf/1207.4161#page=3) ·
[Figure 3, Phases 1–4](https://arxiv.org/pdf/1207.4161#page=7)

## Failure agreement with IDC

[`phase_four_fails_iff_idc_joint_fails`](../../OpenCausalScience/Papers/Tian2004/ExactConditionalDecision.lean)
proves that Tian returns `FAIL` exactly when the joint query after
IDC's Rule 2 exchanges has a nonintrinsic district in its ancestral
graph. The result holds for every exhausted exchange sequence on a
finite acyclic directed mixed graph, including bows. The treatment,
outcome, and evidence sets are pairwise disjoint. The Lean statement
supplies a topological rank for the directed edges and excludes
undirected edges. Such a sequence always exists by
[`exists_exhausted_exchange_run`](../../OpenCausalScience/Papers/Tian2004/ConditionalDecision.lean).

- [`phase_three_iff_marked`](../../OpenCausalScience/Papers/Tian2004/FactorClosure.lean)
  connects the Phase 3 worklist to closure under shared summed arguments.
  An evidence vertex or a treatment is never a summed argument. Any
  parent outside the ancestral graph is a treatment and cannot affect
  either Phase 3 propagation or the Phase 4 outcome test.
- [`rule_two_path_separated_iff_not_linked`](../../OpenCausalScience/Papers/Tian2004/RuleTwoQuery.lean)
  shows that IDC can exchange an evidence vertex exactly when its
  district cannot reach an outcome through those factor connections.
  [`district_eq_after_move`](../../OpenCausalScience/Papers/Tian2004/Reduction.lean)
  shows that each outcome-linked district keeps the same vertex set
  after the exchange.
- [`query_component_identify_iff_intrinsic`](../../OpenCausalScience/Papers/Tian2004/QueryIntrinsic.lean)
  checks each original Phase 2 `Identify` call using the full graph's
  fixing criterion. The underlying proof matches each ancestry and
  district step with legal fixing and proves that an ancestor fixed
  point blocks the target. [Graphical fixing proof](../../OpenCausalScience/Papers/Tian2004/IntrinsicIdentify.lean)

On the IDC side, the comparison uses Shpitser's Proposition 1 for
the exact reduced joint query. The Lean theorem compares the two graph
decisions. Interpreting their agreement as a causal identification
result uses the published conditional-to-joint theorem with its causal
model and positivity assumptions. The symbolic probability expressions
returned on success are outside the verified scope. [Shpitser (2023), Proposition 1](https://arxiv.org/pdf/2307.03750v1#page=7) ·
[Kivva, Etesami, and Kiyavash (2023), Theorems 3–4](https://proceedings.mlr.press/v216/kivva23a.html)

Shpitser's 2007 Appendum already states completeness and explains the
notation in the original example. The [IDC companion](shpitser-pearl-2006-conditional-idc.md#figure-1c-and-the-2007-appendum)
replays that example. This Lean derivation uses the exact-query district
criterion in the 2023 note. [UCLA R-329-APPENDUM](https://ftp.cs.ucla.edu/pub/stat_ser/r329-appendum.pdf)

## Independent finite comparison

The [replay](../../replay/compare-tian-idc.py) implements Tian's district
recursion and IDC's exchange and fixing decisions separately. It checks
each Rule 2 test by edge-marked simple paths and by ancestral moralization
after introducing a latent root for each bidirected edge. With `--cga`,
the released CGA `m_separated_sets` supplies a third separation check.

| Finite domain | Graphs | Queries | Both return `FAIL` | Different decisions |
| --- | ---: | ---: | ---: | ---: |
| Four vertices, all graphs in one topological order | 4,096 | 716,800 | 150,065 | 0 |
| Five vertices, deterministic graph sample | 256 | 199,936 | 68,464 | 0 |

Each graph uses all disjoint treatment, outcome, and evidence assignments
with a nonempty outcome, including empty treatments or evidence. All
846,219 Rule 2 tests agreed across the three separation implementations.
The reported run also checked four fixtures and used the
[CGA v0.2.0a1 wheel](https://github.com/snu-causality-lab/cga/releases/tag/v0.2.0a1).

```sh
python3 replay/compare-tian-idc.py --smoke
python3 replay/compare-tian-idc.py --sample-five 256 --cga
```

The first command is a bounded smoke check. The second reproduces the
table when the CGA wheel is installed.

# Lean modules and names

`OpenCausalScience.Core` is the entry point for shared mathematical definitions and theorems. It currently imports finite DAGs and d-separation. Import the specific module when only one is needed.

```text
OpenCausalScience.lean
OpenCausalScience/
  Core.lean
  Graph/
    DAG.lean
    DSeparation.lean
  Papers.lean
  Papers/
    JeongEtAl2022/Lemma4.lean
    VanDerZanderEtAl2023/AugmentationParentPairs.lean
    WitteEtAl2020/Figure2B.lean
    WitteEtAl2020/Figure2F.lean
  Examples/DSeparation.lean
  Axioms.lean
```

**Shared theory.** Name modules by topic. Extend `Graph/` with graph objects and separation or equivalence results. `Probability/` and `CausalModel/` can supply distribution and intervention semantics to `Identification/` and `Adjustment/`. `Discovery/` can hold PC, GES and FCI results, with graph-level assumptions and oracle or score assumptions stated where they are used. Add each topic as its definitions or results are formalized. Imports in shared theory follow mathematical prerequisites. For example, a theorem about graph paths can import `Graph/` modules directly.

**Published results.** Group a paper's formalizations in `Papers/<WorkId>/`, with a module for a coherent result. Use names such as `Figure2B`, `Lemma4`, or `AugmentationParentPairs`. Cite the exact original statement and any later correction in the file and the [paper checks](paper-checks.md). A corrigendum is a separately citable work, so its own formalization may have its own `WorkId`. Add new paper modules to `Papers.lean` so the default `lake build` checks them. When one paper uses a general theorem established in another, shared theory can supply the theorem while each paper module records its use and hypotheses.

**Examples and verification.** Put general reference examples under `Examples/` and published figures beside the paper result. Keep the axiom inspection commands in `Axioms.lean`, keyed by declaration name. In the paper record, distinguish a calculation on a concrete graph, a theorem quantified over a class of models, and a proof that an implementation meets a specification. For a counterexample, show which hypotheses hold and which conclusion fails. Record a corrected theorem with its own assumptions and conclusion. The release or toolchain revision, source version, theorem name, and precise mathematical statement identify what was checked.

## Paper records

Use one Markdown record per paper in `docs/papers/`, with a stable filename such as `witte-et-al-2020-efficient-adjustment.md`. Give the record a level-one title followed by a topic comment such as `<!-- topic: Adjustment -->`. Use sections within the record for multiple figures, statements, or connected versions.

Link new references directly to the record, adding a section fragment when useful. Older links into `paper-checks.md` are retained through `index-anchor` and `topic-anchor` comments. Keep those comments when updating an existing record.

An established counterexample, author correction, or checked discrepancy can be surfaced after the paper index link using a one-line callout. Name the affected statement and point to the section that gives the evidence and scope. The index uses that same line for its summary.

```markdown
> **Verified counterexample** · [Theorem 2, necessity](#where-the-selected-only-rc-procedure-stops) · RC stops on a graph where selected-only adjustment recovers the effect.
```

The other supported labels are **Author correction** and **Verified discrepancy**. Published examples that illustrate a theorem already stated in the paper stay in their ordinary sections.

Regenerate the topic index after adding or editing a record.

```sh
python3 scripts/build-paper-index.py
python3 scripts/build-paper-index.py --check
```

## Naming

- Use `UpperCamelCase` for modules, namespaces, structures and inductive types, `lowerCamelCase` for executable definitions such as `dSeparated`, and `snake_case` for new theorems such as `no_directed_cycle`. Preserve standard acronyms in graph type names such as `DAG`. [Lean standard library naming conventions](https://github.com/leanprover/lean4/blob/v4.36.0/doc/std/naming.md)
- Name general theorems for their mathematical conclusions. Put paper numbering in the module or the source citation, where readers can match it to the original statement. Use the object namespace for theorems about one object, as in `OpenCausalScience.DAG.no_directed_cycle`.
- Use a stable `WorkId` made from author names and publication year, such as `ShpitserPearl2006` or `WitteEtAl2020`. Use `EtAl` for three or more authors and add a short title when author and year are ambiguous. Record the DOI or source version in the paper record. Use the full module path as the namespace for a new paper-local result.
- The root `import OpenCausalScience` loads the core, examples, and paper checks. The former flat module imports still load their relocated definitions. Existing theorem names such as `OpenCausalScience.WitteFigure2B.candidateSetsFailToSeparate` remain usable.

## Downstream projects

Paper projects can pin a revision of the shared package and import the modules they need. Keep unpublished statements and their private dependencies in the corresponding private Lean repository or paper repository. An anonymous artifact needs its own review of identifying metadata and dependency URLs. The formalization records and the CGA implementation can refer to the same published statement by its source and location.

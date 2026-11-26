# Lee and Bareinboim (2018), structural causal bandits

<!-- topic: Causal decision making -->
<!-- index-anchor: lee-and-bareinboim-2018-structural-causal-bandits -->

[Paper index](../paper-checks.md)

> **Author correction** · [Theorem 9, enumeration proof](#the-enumeration-proof) · The revised proof treats nested and excluded territories in the enumeration and keeps the theorem’s conclusion.

## The enumeration proof

*Structural Causal Bandits: Where to Intervene?*, NeurIPS 2018. The paper repository contains both the Python implementation and a Lean package for MIS and POMIS, including the Lean version of the POMIS enumeration algorithm and its correctness theorem (`Mec.Scb2018.thm9`). The formalization records its assumptions and follows the statement numbers in the author-hosted, unofficial proof update of 2026-11-23. [Proceedings](https://papers.neurips.cc/paper_files/paper/2018/hash/c0a271bc0ecb776a094786474322cb82-Abstract.html) · [Lean scope and build](https://github.com/sanghack81/SCMMAB-NIPS2018/blob/49b6c9f/lean/README.md) · [Python code](https://github.com/sanghack81/SCMMAB-NIPS2018/tree/49b6c9f/npsem)

## Figure 2 replay

On the six-vertex graph from Figure 2, the Python implementation at `49b6c9f` returns the interventional border `{S, T}`, the POMISs `{{S, T}, {T, W}, {T, W, X}}`, and 18 MISs. These agree with the Lean results for that input. [Python enumerators](https://github.com/sanghack81/SCMMAB-NIPS2018/blob/49b6c9f/npsem/where_do.py) · [Lean Figure 2](https://github.com/sanghack81/SCMMAB-NIPS2018/blob/49b6c9f/lean/MecLean/Scb2018/Fig2.lean)

Run this example from the root of the paper repository at that revision.

```python
from npsem.model import CausalDiagram
from npsem.where_do import MISs, MUCT_IB, POMISs

graph = CausalDiagram(
    "STWXYZ",
    [("S", "W"), ("W", "Y"), ("T", "X"), ("T", "Y"), ("Z", "X"), ("X", "Y")],
    [("W", "X", "u_WX"), ("Z", "Y", "u_ZY")],
)
assert MUCT_IB(graph, "Y") == (frozenset("WXYZ"), frozenset("ST"))
assert POMISs(graph, "Y") == {frozenset("ST"), frozenset("TW"), frozenset("TWX")}
assert len(MISs(graph, "Y")) == 18
```

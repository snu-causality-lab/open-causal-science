#!/usr/bin/env python3
"""Check Lean and CGA constrained separators against a simple-path subset oracle.

Install CGA, then pass its source checkout for the independent test oracle and
graph fixtures. The Lean export uses the graph families from MixedSeparation.lean.
Each query object contains left, right, required, allowed, and result. Sets are
lists of zero-based vertex indices. A null result signals that no cut exists.
"""

from __future__ import annotations

import argparse
import json
import sys
from itertools import combinations, product
from pathlib import Path

from causal_graph_algorithms import (
    SeparatorNotFound,
    SeparatorSet,
    find_minimal_m_separator,
)


Vertices = frozenset[str]
Query = tuple[Vertices, Vertices, Vertices, Vertices]
QUERY_FIELDS = ("left", "right", "required", "allowed")


def query_universe(nodes: tuple[str, ...]) -> set[Query]:
    queries = set()
    for labels in product(range(5), repeat=len(nodes)):
        left, right, required, optional = (
            frozenset(node for node, label in zip(nodes, labels, strict=True) if label == tag)
            for tag in range(1, 5)
        )
        if left and right:
            queries.add((left, right, required, required | optional))
    return queries


def parse_vertices(values: object, nodes: tuple[str, ...]) -> Vertices:
    if not isinstance(values, list) or any(
        type(index) is not int or index < 0 or index >= len(nodes) for index in values
    ):
        raise ValueError(f"invalid vertex list {values!r}")
    if len(values) != len(set(values)):
        raise ValueError(f"duplicate vertices in {values!r}")
    return frozenset(nodes[index] for index in values)


def parse_rows(rows: object, nodes: tuple[str, ...]) -> dict[Query, Vertices | None]:
    verdicts = {}
    if not isinstance(rows, list):
        raise ValueError("expected a list of query objects")
    for row in rows:
        if not isinstance(row, dict) or row.keys() != {*QUERY_FIELDS, "result"}:
            raise ValueError(f"invalid separator query row {row!r}")
        query = tuple(parse_vertices(row[name], nodes) for name in QUERY_FIELDS)
        if query in verdicts:
            raise ValueError(f"duplicate separator query {query!r}")
        result = row["result"]
        verdicts[query] = None if result is None else parse_vertices(result, nodes)
    return verdicts


def oracle_cuts(oracle, nodes, edges, query: Query) -> set[Vertices]:
    left, right, required, allowed = query
    optional = tuple(sorted(allowed - required))
    minimal: set[Vertices] = set()
    for count in range(len(optional) + 1):
        for subset in combinations(optional, count):
            cut = required.union(subset)
            if not any(previous < cut for previous in minimal):
                if oracle(nodes, edges, left, right, cut):
                    minimal.add(cut)
    return minimal


def compare_graph(fixtures, family, name, nodes, edges, rows) -> int:
    verdicts = parse_rows(rows, nodes)
    if verdicts.keys() != query_universe(nodes):
        raise ValueError(f"{name}: exported constraints differ from the query universe")
    graph = fixtures.admg(nodes, edges) if family == "ADMG" else fixtures.ancestral_graph(nodes, edges)
    for query, lean_cut in verdicts.items():
        left, right, required, allowed = query
        expected = oracle_cuts(fixtures.m_separated_by_simple_edge_paths, nodes, edges, query)
        result = find_minimal_m_separator(graph, left, right, required=required, allowed=allowed)
        if isinstance(result, SeparatorSet):
            cga_cut = frozenset(result.vertices)
        elif isinstance(result, SeparatorNotFound):
            cga_cut = None
        else:
            raise ValueError(f"{name}: unexpected CGA result {result!r}")
        choices = expected if expected else {None}
        if lean_cut not in choices or cga_cut not in choices:
            raise ValueError(
                f"{name}, query {query!r}: Lean={lean_cut!r}, "
                f"CGA={cga_cut!r}, oracle minimal cuts={expected!r}"
            )
    return len(verdicts)


def compare_export(fixtures, exported: object) -> tuple[int, int]:
    if not isinstance(exported, dict) or exported.keys() != {
        "admg3", "ancestral3", "bow4", "ancestral4"
    }:
        raise ValueError("export has missing or unexpected graph families")
    cases = {code: fixtures.ancestral3_edges(code) for code in range(125)}
    ancestral_cases = {
        code: edges for code, edges in cases.items()
        if fixtures.endpoint_graph_is_ancestral_by_definition(fixtures.NODES3, edges)
    }
    admg_rows = fixtures.indexed_entries(exported["admg3"], "ADMG")
    ancestral_rows = fixtures.indexed_entries(exported["ancestral3"], "ancestral")
    if admg_rows.keys() != set(range(64)) or ancestral_rows.keys() != ancestral_cases.keys():
        raise ValueError("exported graph codes differ from the graph universe")
    comparisons = 0
    for code, rows in admg_rows.items():
        comparisons += compare_graph(
            fixtures, "ADMG", f"ADMG {code}", fixtures.NODES3, fixtures.admg3_edges(code), rows
        )
    for code, rows in ancestral_rows.items():
        comparisons += compare_graph(
            fixtures, "ancestral", f"ancestral {code}", fixtures.NODES3, ancestral_cases[code], rows
        )
    comparisons += compare_graph(
        fixtures, "ADMG", "bow4", fixtures.NODES4, fixtures.BOW4, exported["bow4"]
    )
    comparisons += compare_graph(
        fixtures, "ancestral", "ancestral4", fixtures.NODES4, fixtures.ANCESTRAL4,
        exported["ancestral4"],
    )
    return len(admg_rows) + len(ancestral_rows) + 2, comparisons


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("export", type=Path, help="JSON from the Lean separator replay")
    parser.add_argument("--cga-checkout", type=Path, required=True, help="CGA source checkout")
    args = parser.parse_args()
    tests = args.cga_checkout.resolve() / "tests"
    if not (tests / "compare_lean_mixed_separation.py").is_file():
        parser.error("--cga-checkout must contain the CGA mixed-separation comparison")
    sys.path.insert(0, str(tests))
    import compare_lean_mixed_separation as fixtures

    try:
        exported = json.loads(args.export.read_text(encoding="utf-8"),
                              object_pairs_hook=fixtures.unique_object)
        graphs, comparisons = compare_export(fixtures, exported)
    except (OSError, ValueError) as error:
        raise SystemExit(str(error)) from error
    print(f"{graphs} mixed graphs, {comparisons} Lean/CGA constrained separator checks agree "
          "with the simple-path subset oracle")


if __name__ == "__main__":
    main()

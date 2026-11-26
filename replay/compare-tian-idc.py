#!/usr/bin/env python3
"""Compare FAILURE decisions for Tian (2004) Fig. 3 and IDC on small ADMGs.

Public algorithm sources:
  Tian (2004), Figures 1 and 3: https://arxiv.org/pdf/1207.4161
  Shpitser and Pearl (2008), Figure 7: https://jmlr.org/papers/volume9/shpitser08a/shpitser08a.pdf
  Intrinsic fixing: https://arxiv.org/html/2307.03750

The default run exhausts all 4-node ADMGs consistent with 0 < 1 < 2 < 3.
A pair may carry both edge types. Names and edge order are zero-based and
lexicographic. A query assigns each vertex to one of Y, X, Z, or unused
with Y nonempty. The run checks decisions, never expressions or SCMs.
Use --smoke for bounded local checking. Use --cga for a third separation
oracle if the causal_graph_algorithms package is available on PYTHONPATH.
"""
import argparse
from functools import lru_cache
from itertools import combinations, product
import json
import platform
import random
import sys


@lru_cache(maxsize=None)
def nodes(mask):
    return tuple(i for i in range(mask.bit_length()) if mask & (1 << i))


def mask(vertices):
    return sum(1 << v for v in set(vertices))


class ComparisonFailure(Exception):
    def __init__(self, kind, **details):
        self.details = {"kind": kind, **details}


class Graph:
    def __init__(self, n, directed, bidirected):
        self.n = n
        self.universe = (1 << n) - 1
        self.directed = tuple(directed)
        self.bidirected = tuple(bidirected)
        self.parents = [0] * n
        self.children = [0] * n
        self.spouses = [0] * n
        for a, b in self.directed:
            self.parents[b] |= 1 << a
            self.children[a] |= 1 << b
        for a, b in self.bidirected:
            self.spouses[a] |= 1 << b
            self.spouses[b] |= 1 << a

        # Cache only within a graph so no input survives into the next graph.
        self.ancestors = lru_cache(maxsize=None)(self._ancestors)
        self.districts = lru_cache(maxsize=None)(self._districts)
        self.tian_identify = lru_cache(maxsize=None)(self._tian_identify)
        self.intrinsic = lru_cache(maxsize=None)(self._intrinsic)
        self.mutilated_edges = lru_cache(maxsize=None)(self._mutilated_edges)
        self.inclusive_parents = lru_cache(maxsize=None)(self._inclusive_parents)
        self.names = tuple(str(i) for i in range(n))

    def _ancestors(self, seeds, within):
        reached = seeds
        # Descending topological order makes one pass sufficient.
        for v in reversed(nodes(within)):
            if reached & (1 << v):
                reached |= self.parents[v] & within
        return reached

    def _districts(self, within):
        parts = []
        remaining = within
        while remaining:
            part = remaining & -remaining
            pending = part
            remaining ^= part
            while pending:
                vertex = pending & -pending
                pending ^= vertex
                neighbors = self.spouses[vertex.bit_length() - 1] & remaining
                part |= neighbors
                pending |= neighbors
                remaining ^= neighbors
            parts.append(part)
        return tuple(parts)

    def _inclusive_parents(self, district):
        result = district
        for v in nodes(district):
            result |= self.parents[v]
        return result

    def _tian_identify(self, target, containing):
        ancestors = self.ancestors(target, containing)
        if ancestors == target:
            return True
        if ancestors == containing:
            return False
        part = next(c for c in self.districts(ancestors) if c & target)
        assert target & part == target
        return self.tian_identify(target, part)

    def tian(self, x, y, z):
        ancestral = self.ancestors(y | z, self.universe ^ x)
        summed = ancestral & ~(y | z)
        full_districts = self.districts(self.universe)
        identified = []
        failed = []
        dependency = 0
        for district in self.districts(ancestral):
            containing = next(c for c in full_districts if c & district)
            scope = self.inclusive_parents(district)
            if self.tian_identify(district, containing):
                identified.append((district, scope))
            else:
                failed.append(district)
                dependency |= scope
        pulled_in = []
        while True:
            newly_summed = dependency & summed
            others = []
            for district, scope in identified:
                if scope & newly_summed:
                    dependency |= scope
                    pulled_in.append(district)
                else:
                    others.append((district, scope))
            if len(others) == len(identified):
                break
            identified = others
        return bool(dependency & y), (ancestral, failed, pulled_in, dependency)

    def _intrinsic(self, target):
        # Incoming edges of fixed vertices are deleted. Both relations among
        # random vertices are therefore those in the induced remaining graph.
        remaining = set(range(self.n))
        protected = set(nodes(target))
        while remaining != protected:
            for v in sorted(remaining - protected):
                district = {v}
                pending = [v]
                while pending:
                    a = pending.pop()
                    for b in nodes(self.spouses[a]):
                        if b in remaining and b not in district:
                            district.add(b)
                            pending.append(b)
                strict_descendants = set()
                pending = [v]
                while pending:
                    a = pending.pop()
                    for b in nodes(self.children[a]):
                        if b in remaining and b not in strict_descendants:
                            strict_descendants.add(b)
                            pending.append(b)
                if district.isdisjoint(strict_descendants):
                    remaining.remove(v)
                    break
            else:
                return False
        return True

    def _mutilated_edges(self, x, moved_vertex):
        directed = tuple((a, b) for a, b in self.directed if a != moved_vertex and not (x & (1 << b)))
        bidirected = tuple((a, b) for a, b in self.bidirected if not (x & ((1 << a) | (1 << b))))
        return directed, bidirected

    def idc(self, x, y, z, counters, cga):
        moved = []
        while z:
            for vertex in nodes(z):
                singleton = 1 << vertex
                given = x | (z ^ singleton)
                directed, bidirected = self.mutilated_edges(x, vertex)
                via_paths = path_separated(self.n, directed, bidirected, vertex, y, given)
                via_moral = moral_separated(self.n, directed, bidirected, vertex, y, given)
                counters["rule2_tests"] += 1
                if via_paths != via_moral:
                    raise ComparisonFailure("separation", vertex=vertex, current_x=nodes(x),
                                            current_z=nodes(z), paths=via_paths, moral=via_moral)
                if cga is not None:
                    raw = cga.DirectedBidirectedGraph(
                        nodes=self.names,
                        directed=((str(a), str(b)) for a, b in directed),
                        bidirected=((str(a), str(b)) for a, b in bidirected),
                    )
                    graph = cga.AcyclicDirectedBidirectedGraph(raw)
                    via_cga = cga.m_separated_sets(graph, str(vertex), map(str, nodes(y)),
                                                     map(str, nodes(given)))
                    counters["cga_rule2_tests"] += 1
                    if via_paths != via_cga:
                        raise ComparisonFailure("cga_separation", vertex=vertex, current_x=nodes(x),
                                                current_z=nodes(z), paths=via_paths, cga=via_cga)
                if via_paths:
                    moved.append(vertex)
                    x |= singleton
                    z ^= singleton
                    break
            else:
                break

        # Build the remaining joint outcome's ancestor set with a worklist.
        relevant = set(nodes(y | z))
        pending = list(relevant)
        removed = set(nodes(x))
        while pending:
            v = pending.pop()
            for a, b in self.directed:
                if b == v and a not in removed and a not in relevant:
                    relevant.add(a)
                    pending.append(a)

        # Independently merge the sets of endpoints of bidirected edges.
        partition = {v: {v} for v in relevant}
        for a, b in self.bidirected:
            if a in relevant and b in relevant and partition[a] is not partition[b]:
                union = partition[a] | partition[b]
                for v in union:
                    partition[v] = union
        district_masks = sorted({mask(part) for part in partition.values()})
        failed = [part for part in district_masks if not self.intrinsic(part)]
        return bool(failed), (moved, x, z, mask(relevant), failed)


def path_separated(n, directed, bidirected, start, target, given):
    """Enumerate simple edge-labelled paths. A bow contributes two choices."""
    edges = [[] for _ in range(n)]
    collider_ancestors = given
    for a, b in reversed(directed):
        if collider_ancestors & (1 << b):
            collider_ancestors |= 1 << a
    for a, b in directed:
        edges[a].append((b, False, True))
        edges[b].append((a, True, False))
    for a, b in bidirected:
        edges[a].append((b, True, True))
        edges[b].append((a, True, True))

    def active_path(current, incoming_arrow, seen):
        if (1 << current) & target:
            return True
        for neighbor, here_arrow, next_arrow in edges[current]:
            next_bit = 1 << neighbor
            if next_bit & seen:
                continue
            if incoming_arrow is not None:
                current_bit = 1 << current
                if incoming_arrow and here_arrow:
                    if not (current_bit & collider_ancestors):
                        continue
                elif current_bit & given:
                    continue
            if active_path(neighbor, next_arrow, seen | next_bit):
                return True
        return False

    return not active_path(start, None, 1 << start)


def moral_separated(n, directed, bidirected, start, target, given):
    """Replace each bidirected edge by a latent fork, then moralize ancestors."""
    observed_target = set(nodes(target))
    conditioning = set(nodes(given))
    parents = [set() for _ in range(n + len(bidirected))]
    for a, b in directed:
        parents[b].add(a)
    for latent, (a, b) in enumerate(bidirected, n):
        parents[a].add(latent)
        parents[b].add(latent)
    ancestors = {start} | observed_target | conditioning
    pending = list(ancestors)
    while pending:
        vertex = pending.pop()
        new_parents = parents[vertex] - ancestors
        ancestors.update(new_parents)
        pending.extend(new_parents)
    moral = {v: set() for v in ancestors}
    for child in ancestors:
        for parent in parents[child]:
            moral[child].add(parent)
            moral[parent].add(child)
            moral[parent].update(parents[child] - {parent})
    reached = {start}
    pending = [start]
    while pending:
        vertex = pending.pop()
        new = moral[vertex] - conditioning - reached
        if new & observed_target:
            return False
        reached.update(new)
        pending.extend(new)
    return True


def queries(n):
    for roles in product(range(4), repeat=n):
        if 1 in roles:
            yield tuple(mask(v for v, role in enumerate(roles) if role == number) for number in (2, 1, 3))


def compare(graph, x, y, z, counters, cga, code=None, expected=None):
    try:
        tian_fail, (d, unrecognized, pulled_in, scope) = graph.tian(x, y, z)
        idc_fail, (moved, new_x, new_z, joint_ancestors, failed) = graph.idc(x, y, z, counters, cga)
        counters["queries"] += 1
        counters["tian_fail"] += int(tian_fail)
        counters["idc_fail"] += int(idc_fail)
        counters["joint_idc_fail"] += int(idc_fail and not z)
        counters["conditional_queries"] += int(bool(z))
        if tian_fail != idc_fail or (expected is not None and tian_fail != expected):
            raise ComparisonFailure(
                "algorithm_decision" if expected is None else "fixture_decision",
                tian_fail=tian_fail,
                idc_fail=idc_fail,
                expected_fail=expected,
                tian_ancestral_set=nodes(d),
                tian_unidentified=[nodes(v) for v in unrecognized],
                tian_additional_terms=[nodes(v) for v in pulled_in],
                tian_factor_scope=nodes(scope),
                idc_rule2_order=moved,
                idc_x=nodes(new_x),
                idc_z=nodes(new_z),
                idc_joint_ancestors=nodes(joint_ancestors),
                idc_nonintrinsic=[nodes(v) for v in failed],
            )
    except ComparisonFailure as error:
        print(json.dumps({
            "event": "disagreement", "n": graph.n, "code": code,
            "directed": graph.directed, "bidirected": graph.bidirected,
            "x": nodes(x), "y": nodes(y), "z": nodes(z), **error.details,
        }, sort_keys=True), flush=True)
        raise


def graph_from_code(n, graph_code):
    pairs = tuple(combinations(range(n), 2))
    directed = tuple(pair for i, pair in enumerate(pairs) if graph_code & (1 << i))
    bidirected = tuple(pair for i, pair in enumerate(pairs) if graph_code & (1 << (i + len(pairs))))
    return Graph(n, directed, bidirected)


def empty_counters():
    return dict(queries=0, tian_fail=0, idc_fail=0, joint_idc_fail=0,
                conditional_queries=0, rule2_tests=0, cga_rule2_tests=0)


def run(n, codes, expected_graphs, cga, kind, seed=None):
    assignments = tuple(queries(n))
    assert len(assignments) == 4**n - 3**n
    counters = empty_counters()
    graph_count = 0
    bow_count = 0
    try:
        for code in codes:
            graph = graph_from_code(n, code)
            graph_count += 1
            bow_count += int(bool(set(graph.directed) & set(graph.bidirected)))
            for x, y, z in assignments:
                compare(graph, x, y, z, counters, cga, code=code)
    finally:
        print(json.dumps({
            "event": "summary", "kind": kind, "n": n, "seed": seed,
            "graphs_seen": graph_count, "graphs_with_bows": bow_count,
            "expected_graphs": expected_graphs, "queries_per_complete_graph": len(assignments),
            "expected_queries": expected_graphs * len(assignments),
            "python": platform.python_version(), **counters,
        }, sort_keys=True), flush=True)
    assert graph_count == expected_graphs
    assert counters["queries"] == expected_graphs * len(assignments)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smoke", action="store_true", help="run fixtures and 28 two-node queries only")
    parser.add_argument("--cga", action="store_true", help="also compare with causal_graph_algorithms")
    parser.add_argument("--sample-five", type=int, default=0, help="sample this many distinct 5-node graphs")
    parser.add_argument("--seed", type=int, default=2601126)
    args = parser.parse_args()
    if args.sample_five < 0 or args.sample_five > (1 << 20):
        parser.error("--sample-five must be between 0 and 1048576")
    if args.smoke and args.sample_five:
        parser.error("--smoke precludes the five-node sample")
    cga = None
    if args.cga:
        import causal_graph_algorithms as cga
        print(json.dumps({"event": "cga_source", "module": cga.__file__}), flush=True)

    fixtures = (
        # Original UAI 2006 Fig. 1(c), named X=0,W=1,Y=2,Z=3.
        (Graph(4, ((0, 3), (1, 2), (2, 3)), ((0, 3),)), 1, 2, 8, True),
        # The unidentified bow term can be canceled for an unrelated outcome.
        (Graph(3, ((0, 2),), ((0, 2),)), 1, 2, 4, False),
        # A bow obstructs unconditional ID.
        (Graph(2, ((0, 1),), ((0, 1),)), 1, 2, 0, True),
        # A mediator observed in a DAG can be moved to an intervention.
        (Graph(3, ((0, 1), (1, 2)), ()), 1, 4, 2, False),
    )
    counters = empty_counters()
    for graph, x, y, z, expected in fixtures:
        compare(graph, x, y, z, counters, cga, expected=expected)
    print(json.dumps({"event": "fixtures_passed", "count": len(fixtures)}, sort_keys=True), flush=True)

    n = 2 if args.smoke else 4
    count = 1 << (n * (n - 1))
    run(n, range(count), count, cga, "exhaustive")
    if args.sample_five:
        codes = sorted(random.Random(args.seed).sample(range(1 << 20), args.sample_five))
        run(5, codes, args.sample_five, cga, "deterministic_sample", args.seed)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except ComparisonFailure:
        sys.exit(1)

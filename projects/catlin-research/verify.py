#!/usr/bin/env python3
"""Exact independent finite checks. This is not a Lean proof checker."""
from __future__ import annotations
import csv
import json
from itertools import combinations, product
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def adjacent(u: int, v: int) -> bool:
    a, b = u // 3, v // 3
    return u != v and (a == b or (a + 1) % 5 == b or (b + 1) % 5 == a)

def resource_bound(b: tuple[int, ...]) -> tuple[int, int, int]:
    missing = sum(b[i] * b[(i + 2) % 5] for i in range(5))
    extra = sum(max(0, b[i] * b[(i + 2) % 5] - (3 - b[(i + 1) % 5]))
                for i in range(5))
    return missing, extra, missing + extra

def main() -> None:
    vertices = list(range(15))
    edges = [(u, v) for u, v in combinations(vertices, 2) if adjacent(u, v)]
    assert len(edges) == 60
    colour_classes = [(0, 6), (1, 7), (2, 9), (3, 10), (4, 11),
                      (5, 12), (8, 13), (14,)]
    colours = {v: c for c, group in enumerate(colour_classes) for v in group}
    assert set(colours) == set(vertices)
    assert all(colours[u] != colours[v] for u, v in edges)
    triples = list(combinations(vertices, 3))
    assert all(any(adjacent(u, v) for u, v in combinations(t, 2)) for t in triples)
    rows = []
    for b in product(range(4), repeat=5):
        if sum(b) != 8:
            continue
        missing, extra, required = resource_bound(b)
        assert required >= 12, (b, required)
        rows.append((*b, missing, extra, required))
    assert len(rows) == 155
    assert min(row[-1] for row in rows) == 12
    with (ROOT / 'all_155_branch_profiles.csv').open('w', newline='', encoding='utf-8') as f:
        writer = csv.writer(f)
        writer.writerow(['b0', 'b1', 'b2', 'b3', 'b4', 'missing_pairs',
                         'extra_internal_vertices', 'required_internal_vertices'])
        writer.writerows(rows)
    report = {
        'status': 'PASS: exact Python finite checks only',
        'vertices': 15, 'edges': len(edges),
        'independent_triples_found': 0, 'unordered_triples_checked': len(triples),
        'proper_colour_classes': colour_classes,
        'all_profiles_checked': len(rows), 'minimum_required_internal_vertices': 12,
        'available_internal_vertices_for_K8': 7,
        'lean_compilation': 'See separate GitHub Actions log; not checked by this script.',
        'scope': 'Known Catlin counterexample; NOT full Erdos 717 / JSP-000585.',
        'edges_list': edges,
    }
    (ROOT / 'python_verification.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in report.items() if k != 'edges_list'}, indent=2))

if __name__ == '__main__':
    main()

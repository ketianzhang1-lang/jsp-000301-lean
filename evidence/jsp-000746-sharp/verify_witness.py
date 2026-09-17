#!/usr/bin/env python3
"""Independent exact finite check of the 17-vertex witness (standard library only).

This validates the lower-bound witness, not the universal 18-vertex upper bound.
The latter is established by the separately attributed, kernel-checked Lean proof.
No external optimizer or SAT solver is needed to replay this checker.
"""
from __future__ import annotations
import itertools
import json
import re
from pathlib import Path

EDGES = [
    (1,3),(1,5),(1,7),(1,11),(1,13),(1,15),
    (2,5),(2,6),(2,10),(2,13),(2,14),
    (3,6),(3,8),(3,10),(3,12),
    (4,7),(4,10),(4,11),(4,12),(4,13),
    (5,9),(5,12),(6,7),(6,11),(6,15),
    (7,9),(7,17),(8,9),(8,13),(8,14),(8,15),
    (9,10),(9,11),(10,15),(10,16),(11,14),(11,16),
    (12,14),(12,16),(13,16),(14,17),(15,17),(16,17)]

def check(n: int, edges: set[tuple[int, int]]) -> dict:
    if n < 0:
        raise ValueError('n must be nonnegative')
    if any(not (1 <= a < b <= n) for a,b in edges):
        raise ValueError('Edges must be sorted, distinct endpoints in [1,n].')
    triples = list(itertools.combinations(range(1,n+1),3))
    triangles = [t for t in triples if all(e in edges for e in itertools.combinations(t,2))]
    schur = [(a,b,a+b) for a in range(1,n+1) for b in range(a+1,n+1) if a+b <= n]
    uncovered = [t for t in schur if not any(e in edges for e in itertools.combinations(t,2))]
    return {'n': n, 'edges': len(edges), 'triples_checked': len(triples),
            'schur_triples_checked': len(schur), 'triangles': triangles,
            'independent_schur_triples': uncovered,
            'valid_counterexample': not triangles and not uncovered}

def main() -> None:
    if len(EDGES) != len(set(EDGES)):
        raise AssertionError('Duplicate edge in source')
    source_path = Path(__file__).with_name('JSP000746Sharp.lean')
    if not source_path.exists():
        source_path = Path(__file__).resolve().parents[2]/'projects/jsp-000746-sharp/JSP000746Sharp.lean'
    source = source_path.read_text(encoding='utf-8')
    edge_literal = source.split('def edges : List (Fin 17 × Fin 17) := [',1)[1].split(']',1)[0]
    lean_edges = [(int(a)+1,int(b)+1) for a,b in re.findall(r'\((\d+),\s*(\d+)\)',edge_literal)]
    if lean_edges != EDGES:
        raise AssertionError('Lean source and independently encoded witness disagree')
    edges = set(EDGES)
    results = [check(n, {e for e in edges if e[1] <= n}) for n in range(18)]
    if not all(x['valid_counterexample'] for x in results):
        raise AssertionError(results)
    if not check(17, edges | {(3,5)})['triangles']:
        raise AssertionError('Triangle negative control was not rejected')
    critical = next(e for e in sorted(edges) if check(17, edges-{e})['independent_schur_triples'])
    coverage = []
    for a in range(1,18):
        for b in range(a+1,18):
            if a+b <= 17:
                t = (a,b,a+b)
                covering = [e for e in itertools.combinations(t,2) if e in edges]
                coverage.append({'triple': t, 'covering_edges': covering})
    report = {'scope': 'lower-bound witness only; upper bound not proved by this script',
              'lean_edge_list_matches': True, 'main': results[-1], 'all_initial_intervals': results,
              'degrees': [sum(v in e for e in edges) for v in range(1,18)],
              'negative_controls': {'added_triangle_edge': [3,5],
                                    'deleted_essential_edge': critical, 'both_rejected': True},
              'schur_coverage': coverage}
    destination = Path(__file__).with_name('witness-report.json')
    destination.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(report['main'], indent=2))
    print('Every initial interval n=0,...,17 checked; both negative controls rejected.')
    print('ALL WITNESS CHECKS PASSED')

if __name__ == '__main__':
    main()

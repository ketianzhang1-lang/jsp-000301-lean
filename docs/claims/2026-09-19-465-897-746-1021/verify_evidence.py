"""Verify immutable source bindings, recorded ports and supplementary finite checks.

Requires Python 3, GNU patch and network access, or --source-cache DIR.
This does not execute Lean/NaNoda, establish authorship or decide an award.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import re
import subprocess
import tempfile
from urllib.request import Request, urlopen


def require(condition, message):
    if not condition:
        raise ValueError(message)


def verify(cache=None):
    records = json.loads(Path(__file__).with_name('sources.json').read_text())['sources']
    sources = {}
    for row in records:
        key = row['id']
        if cache is not None:
            data = (cache / (key + '.source')).read_bytes()
        else:
            request = Request(row['url'], headers={'User-Agent': 'JSP-source-review/1.0'})
            with urlopen(request, timeout=45) as response:
                data = response.read()
        actual = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
                  'git_blob_sha1': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()}
        for field, value in actual.items():
            require(value == row[field], f'{key}: {field} differs')
        sources[key] = data
    print(f'PASS {len(records)} source snapshots: byte counts, SHA-256 and Git blobs')
    for n in [465, 897, 746, 1021]:
        require(sources[f'{n}_main_selected'] == sources[f'{n}_main_later'], f'{n}: main proof changed')
        require(sources[f'{n}_lake-manifest.json_selected'] == sources[f'{n}_lake-manifest.json_later'],
                f'{n}: dependency manifest changed')
    for n in [746, 1021]:
        require(sources[f'{n}_supplement_selected'] == sources[f'{n}_supplement_later'],
                f'{n}: supplementary source changed')
        require(sources[f'{n}_UPSTREAM.json_selected'] == sources[f'{n}_UPSTREAM.json_later'],
                f'{n}: upstream source bindings changed')
    for n in [465, 897]:
        require(sources[f'{n}_main_selected'] == sources[f'{n}_main_historical'],
                f'{n}: original submission source differs')
    print('PASS all selected-to-later bindings and the 465/897 original submission files')

    modules = ['Foundations', 'Geometry', 'Subgraphs', 'Counting', 'Coordinates', 'Counterexample', 'Quantitative']
    expected = dict(line.split(None, 1)[::-1] for line in sources['465_upstream_hashes'].decode().splitlines())
    with tempfile.TemporaryDirectory(prefix='jsp465-port-') as tmp:
        root = Path(tmp)
        for name in modules:
            rel = f'ErdosProblems/Erdos180/{name}.lean'
            data = sources[f'465_{name}_upstream']
            require(hashlib.sha256(data).hexdigest() == expected[rel], f'465: upstream manifest mismatch {name}')
            target = root / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        subprocess.run(['patch', '--batch', '--fuzz=0', '-p1', '-d', str(root)],
                       input=sources['465_patch'], capture_output=True, check=True)
        for name in modules:
            require((root / f'ErdosProblems/Erdos180/{name}.lean').read_bytes() == sources[f'465_{name}_ported'],
                    f'465: patch fails to reproduce {name}')
    print('PASS 465: published patch reproduces all seven imported modules exactly')

    require(sources['897_original'] == sources['897_retained'], '897: retained original differs from upstream')
    port = sources['897_original'].decode()
    for module in ['IntervalCases', 'Linarith', 'NormNum']:
        line = f'import Mathlib.Tactic.{module}\n'
        require(port.count(line) == 1, f'897: expected import {module}')
        port = port.replace(line, '')
    port = port.replace('SimpleGraph.cliqueFree_iff_top_free', 'SimpleGraph.cliqueFree_card_iff_free_top')
    port = port.replace('SimpleGraph.card_edgeFinset_turanGraph]', 'SimpleGraph.turanNumber_eq]')
    port = port.replace('SimpleGraph.card_edgeFinset_turanGraph_add', 'SimpleGraph.turanNumber_add')
    old = '    n ^ 2 ≤ 4 * #(SimpleGraph.turanGraph n 2).edgeFinset + 1 := by\n'
    require(port.count(old) == 1, '897: expected induction target missing')
    port = port.replace(old, old + '  change n ^ 2 ≤ 4 * SimpleGraph.turanNumber n 2 + 1\n')
    require(port.encode() == sources['897_ported'], '897: source differs beyond the documented compatibility edits')
    print('PASS 897: retained upstream bytes and the complete compatibility transformation')

    # Recompute finite facts from the selected literal witness, independently of Lean.
    text746 = sources['746_supplement_selected'].decode()
    edge_text = text746.split('def edges : List (Fin 17 × Fin 17) := [', 1)[1].split(']', 1)[0]
    edges = [tuple(map(int, p)) for p in re.findall(r'\((\d+),(\d+)\)', edge_text)]
    require(len(edges) == len(set(edges)) == 43 and all(0 <= a < b < 17 for a, b in edges), '746: malformed edge list')
    edge_set = set(edges)
    adj = lambda a, b: (min(a, b), max(a, b)) in edge_set
    triangles = [t for t in itertools.combinations(range(17), 3) if all(adj(a, b) for a, b in itertools.combinations(t, 2))]
    require(not triangles, '746: witness contains a triangle')
    triples = [(a, b, a+b+1) for a in range(17) for b in range(a+1, 17) if a+b+1 < 17]
    require(all(any(adj(i, j) for i, j in itertools.combinations(t, 2)) for t in triples), '746: uncovered Schur triple')
    print(f'PASS 746: 43 distinct edges, no triangles, all {len(triples)} distinct-summand Schur triples covered')

    text1021 = sources['1021_supplement_selected'].decode()
    table_text = text1021.split('def witnessTable : Array (List (Fin 10)) := #[', 1)[1].split('\n\ndef witness ', 1)[0]
    table = [[int(x) for x in re.findall(r'\d+', row)] for row in re.findall(r'\[([^\[\]]*)\]', table_text)]
    require(len(table) == 196, '1021: witness table length differs')
    def paley(i, j): return (j + 7 - i) % 7 in (1, 2, 4)
    def incoming(c, i): return paley(c % 7, i) if c < 7 else paley(i, c % 7)
    def retained(c, d):
        return (c < 7 <= d and paley(c % 7, d % 7)) or (c >= 7 and d >= 7 and paley(d % 7, c % 7))
    def local_arc(c, d, i, j):
        if i == j: return False
        if i < 7:
            if j < 7: return paley(i, j)
            if j == 7: return True
            return incoming(c if j == 8 else d, i)
        if i == 7: return j >= 8
        if i == 8: return not incoming(c, j) if j < 7 else j == 9
        return not incoming(d, j) if j < 7 else False
    relevant = witnessed = retained_relevant = 0
    for c, d in itertools.product(range(14), repeat=2):
        if sum(incoming(c, i) and incoming(d, i) for i in range(7)) != 1:
            continue
        relevant += 1
        witness = table[14*c+d]
        valid = len(witness) == len(set(witness)) == 5 and all(0 <= i < 10 for i in witness) and all(local_arc(c, d, i, j) for i, j in itertools.combinations(witness, 2))
        require(valid or retained(c, d), f'1021: pair {c},{d} has neither certificate nor retained pattern')
        witnessed += bool(valid)
        retained_relevant += retained(c, d)
    require(sum(retained(c, d) for c, d in itertools.product(range(14), repeat=2)) == 42, '1021: retained count differs')
    def final_arc(i, j):
        if i == j: return False
        if i < 7:
            if j < 7: return paley(i, j)
            return True if j == 7 else paley(i, j-8)
        if i == 7: return j >= 8
        if j < 7: return i-8 == j or paley(i-8, j)
        return False if j == 7 else paley(j-8, i-8)
    literal = re.search(r'\(\[([\d, ]+)\] : List \(Fin 15\)\)', text1021).group(1)
    final_witness = list(map(int, literal.split(',')))
    require(len(final_witness) == len(set(final_witness)) == 5 and all(final_arc(i, j) for i, j in itertools.combinations(final_witness, 2)), '1021: final local witness fails')
    print(f'PASS 1021: 196 pairs examined; {relevant} meet the intersection hypothesis; {witnessed} have checked five-set witnesses; {retained_relevant} retained relevant pairs; 42 retained patterns overall; final five-set checked')
    print('Scope: provenance and supplementary finite computations only. Full Lean proofs rely on their credited upstream theorems and existing CI receipts.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-cache', type=Path)
    verify(parser.parse_args().source_cache)

#!/usr/bin/env python3
"""Exact finite checks for an independent reconstruction of the n=15 proof.
NOT a new mathematical result. NOT a first formalization. NOT Lean verification.
Python 3.10+, standard library only. Run: python verify.py
"""
from __future__ import annotations
from itertools import combinations, permutations, product
import json
from pathlib import Path

Q = {1, 2, 4}
P = [sum(1 << j for j in range(7) if (j - i) % 7 in Q) for i in range(7)]
O = P
I = [127 ^ (P[i] | (1 << i)) for i in range(7)]


def transitive_witness(adj: list[int], vertices: int, size: int) -> tuple[int, ...] | None:
    """Complete search: choose the first vertex and recurse in its out-neighbors."""
    if size == 0:
        return ()
    if vertices.bit_count() < size:
        return None
    remaining = vertices
    while remaining:
        bit = remaining & -remaining
        remaining -= bit
        v = bit.bit_length() - 1
        tail = transitive_witness(adj, vertices & adj[v], size - 1)
        if tail is not None:
            return (v,) + tail
    return None


def check_witness(adj: list[int], w: tuple[int, ...]) -> bool:
    """Directly inspect every ordered edge, independently of the search recursion."""
    return len(set(w)) == len(w) and all(
        (adj[w[i]] >> w[j]) & 1 for i in range(len(w)) for j in range(i + 1, len(w))
    )


def check_tournament(adj: list[int]) -> None:
    n = len(adj)
    assert all(not ((adj[i] >> i) & 1) for i in range(n))
    assert all(((adj[i] >> j) & 1) + ((adj[j] >> i) & 1) == 1
               for i in range(n) for j in range(i + 1, n))


def two_extensions(c: int, d: int) -> list[int]:
    """B=0..6, v=7, a=8, b=9; B->v->a,b and a->b.
    c,d are exactly the B vertices pointing to a,b, respectively.
    """
    adj = [P[i] | (1 << 7) for i in range(7)] + [(1 << 8) | (1 << 9), 1 << 9, 0]
    for k, incoming in enumerate((c, d)):
        a = 8 + k
        for j in range(7):
            if (incoming >> j) & 1:
                adj[j] |= 1 << a
            else:
                adj[a] |= 1 << j
    check_tournament(adj)
    return adj


def label(v: int) -> str:
    return f'B{v}' if v < 7 else ('v', 'a', 'b')[v - 7]


def main() -> None:
    check_tournament(P)
    assert transitive_witness(P, 127, 4) is None
    assert all(row.bit_count() == 3 for row in P)
    assert all((P[i] & P[j]).bit_count() == 1 for i in range(7) for j in range(i+1, 7))
    assert not any(check_witness(P, w) for w in permutations(range(7), 4))

    cyclic = [sum(1 << v for v in s) for s in combinations(range(7), 3)
              if transitive_witness(P, sum(1 << v for v in s), 3) is None]
    assert len(cyclic) == 14 and set(cyclic) == set(O + I)

    classification = []
    for perm in permutations(range(3)):
        adj = [14] + [1 << (1 + (i+1)%3) for i in range(3)] + [1 | (1 << (4+(i+1)%3)) for i in range(3)]
        for i in range(3):
            for j in range(3):
                if j == perm[i]:
                    adj[4+j] |= 1 << (1+i)
                else:
                    adj[1+i] |= 1 << (4+j)
        check_tournament(adj)
        w = transitive_witness(adj, 127, 4)
        if w is not None:
            assert check_witness(adj, w)
            classification.append({'permutation': perm, 'TT4': w})
        else:
            iso = next((p for p in permutations(range(7)) if all(
                ((adj[i] >> j) & 1) == ((P[p[i]] >> p[j]) & 1)
                for i in range(7) for j in range(7))), None)
            assert iso is not None
            classification.append({'permutation': perm, 'isomorphism_to_P7': iso})

    surviving = []
    for c, d in product(cyclic, repeat=2):
        if (c & d).bit_count() != 1:
            continue
        adj = two_extensions(c, d)
        w = transitive_witness(adj, (1 << 10)-1, 5)
        predicted = any((c == O[i] and d == I[j] and (j-i)%7 in Q) or
                        (c == I[i] and d == I[j] and (i-j)%7 in Q)
                        for i in range(7) for j in range(7))
        assert (w is None) == predicted
        if w is None:
            surviving.append([c, d])
        else:
            assert check_witness(adj, w)
    assert len(surviving) == 42

    table = []
    for typ1, typ2, j in product(('O', 'I'), ('O', 'I'), (0, 1, 3)):
        c = (O if typ1 == 'O' else I)[0]
        d = (O if typ2 == 'O' else I)[j]
        inter = (c & d).bit_count()
        row: dict[str, object] = {'C_a': f'{typ1}0', 'C_b': f'{typ2}{j}', 'intersection_size': inter}
        if inter != 1:
            row['outcome'] = 'intersection excludes'
        else:
            w = transitive_witness(two_extensions(c,d), (1 << 10)-1, 5)
            row['outcome'] = 'retained' if w is None else 'TT5 excludes'
            if w is not None:
                row['witness'] = [label(v) for v in w]
        table.append(row)

    for r, t in product(Q, range(7)):
        f = [(r*i+t)%7 for i in range(7)]
        assert len(set(f)) == 7
        assert all(((P[i]>>j)&1) == ((P[f[i]]>>f[j])&1) for i in range(7) for j in range(7))

    adj = [P[i] | (1<<7) | (P[i]<<8) for i in range(7)]
    adj += [sum(1<<j for j in range(8,15))]
    adj += [(I[i]<<8) | P[i] | (1<<i) for i in range(7)]
    check_tournament(adj)
    final = (8, 1, 13, 2, 11)  # A0, B1, A5, B2, A3
    assert check_witness(adj, final)
    assert all(row.bit_count() == 7 for row in adj)

    result = {'status': 'PASS: finite checks only; not Lean verification',
              'novelty': 'NOT NEW: public full Lean proof exists in plby/lean-proofs/Erdos1216',
              'classification_7': classification,
              'cyclic_triples': sorted(cyclic),
              'ordered_cyclic_pairs_checked': 196,
              'pair_lemma_survivors': 42,
              'normalized_table': table,
              'final_TT5': ['A0', 'B1', 'A5', 'B2', 'A3']}
    out = Path(__file__).with_name('verification-results.json')
    out.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()

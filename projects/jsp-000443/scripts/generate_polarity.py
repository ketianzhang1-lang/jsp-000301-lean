#!/usr/bin/env python3
"""Reproduce the finite witness. Diagnostic only: Lean checks its own rows."""
import json
import re
from pathlib import Path


def mul4(a, b):
    """GF(4) = GF(2)[x]/(x^2+x+1), low bit is the constant coefficient."""
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        if a & 4:
            a ^= 7
        b >>= 1
    return result


points = ([(1, a, b) for a in range(4) for b in range(4)]
          + [(0, 1, b) for b in range(4)] + [(0, 0, 1)])
points.remove((1, 1, 0))


def adjacent(p, q):
    return p != q and (mul4(p[0], q[0]) ^ mul4(p[1], q[1]) ^ mul4(p[2], q[2])) == 0


rows = [sum(1 << j for j, q in enumerate(points) if adjacent(p, q)) for p in points]
source = (Path(__file__).resolve().parent.parent / "JSP000443.lean").read_text()
literal = source.split("def row20", 1)[1].split("([", 1)[1].split("] : List", 1)[0]
assert rows == [int(s) for s in re.findall(r"\d+", literal)]
assert min(row.bit_count() for row in rows) == 4
assert max((rows[i] & rows[j]).bit_count() for i in range(20) for j in range(i)) == 1
print(json.dumps({"vertices": 20, "edges": sum(x.bit_count() for x in rows) // 2,
                  "minimum_degree": 4, "maximum_common_neighbors": 1,
                  "rows_match_Lean": True, "rows": rows}, indent=2))

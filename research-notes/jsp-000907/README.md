# JSP-000907 / Erdős 1091 — candidate bounded-chord construction

This package contains a mathematical proof and reproducible finite checks for an infinite family of 4-critical graphs with at most **5 chords on every cycle** and at most **4 chords on every odd cycle**. Both bounds are attained within the family.

## Important status

- The original problem was already solved before this work.
- This proof addresses the entire parameter range of its **second question**, not all questions in the JSP entry.
- The proof is mathematical prose, **not a Lean-checked formal proof**.
- The comparison with a published 10-chord construction is documented in `proof.md`; novelty over all prior literature is not established.
- No prize eligibility, mathematical first priority, submission, or award is claimed.

## Contents

- `proof.md`: definitions, complete proof of the graph-family theorem, uniform consequence, scope and prior work.
- `verify.py`: exact finite checks, independent of the cycle classification used in the proof.
- `verification.json`: machine-readable results from the actual run.
- `verification.log`: run output.
- `requirements.txt`: the NetworkX version used.
- `scope.json`: machine-readable contribution and validation status.

## Reproduce

Python 3.10 or newer:

```sh
python -m pip install -r requirements.txt
python verify.py --max-ell 19 --output verification-rerun.json
```

Do not use Python's `-O` flag, since checks use assertions.

Graph labels: `z = 0`; `v_i = 1 + 4*i`, `a_i = 2 + 4*i`, `b_i = 3 + 4*i`, `c_i = 4 + 4*i`.

For larger parameters, the proof remains the same; finite cycle enumeration and repeated coloring checks can become costly. No run beyond the recorded range is claimed.

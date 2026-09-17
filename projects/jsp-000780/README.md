# JSP-000780 / Erdős 939: infinitely many primitive six-full sums

This package proves the r=6 case of the known binomial construction. It also
refutes the universal finiteness variant: it is false that, for every r ≥ 4,
there are only finitely many primitive sets of r−2 positive r-full summands
whose sum is r-full.

**Scope:** four distinct six-full summands, collective gcd 1, and infinitely
many distinct sums. This is partial scope relative to JSP-000780 as a whole.
It is not a solution of the r=4 question, the r=5 infinitude question, the
three-full triple problem, or the full construction for every r ≥ 6.

## Construction

For every natural t, let a=30(t+11)+1, x=a^6 and y=30^6. Take

- (x−y)^6;
- 12x^5y;
- 40x^3y^3;
- 12xy^5.

Their sum is (x+y)^6. All four summands are positive and six-full. They are
strictly ordered in the reverse order listed, and their collective gcd is 1.
The sum increases strictly with t. No primality assumption on a is needed.

## Main declarations

- `solution_for_every_parameter`: every natural parameter is a valid solution.
- `infinitely_many_solutions`: infinitely many distinct four-element sets.
- `infinitely_many_totals`: infinitely many distinct sums.
- `original_six_infinite`: the result with the original prime-factor predicate.
- `not_finite_for_every_r`: the negative universal-finiteness statement.

See [STATEMENT.md](STATEMENT.md), [PROVENANCE.md](PROVENANCE.md), and
[VERIFICATION.md](VERIFICATION.md) for scope, attribution and actual checks.

## Reproduce

Install the toolchain in `lean-toolchain`, then run:

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The lockfile pins Lean/Mathlib 4.34.0 and nine library dependencies. The
NaNoda script pins both the exporter and checker and permits only
`propext`, `Classical.choice`, and `Quot.sound`.

## Review request

Proposed formalization recipient: `RECIPIENT-JSP-000780-KZ-A`, confirmation
pending. The submitter coordinated the OpenAI ChatGPT-assisted implementation
and has an interest in its assessment. Please assess mathematical fidelity,
partial-scope eligibility, attribution, overlap and priority. No award,
first-formalization priority, independent human verification or payment
entitlement is asserted. The existing mathematical attribution is retained.

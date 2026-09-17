# JSP-000947: complete classification through 2^44

This Lean project proves the complete finite-range variant of JSP-000947 /
Erdős problem 1142:

```text
{n : Nat | n <= 2^44 and n > 2 and
  for every k > 0 with 2^k < n, n - 2^k is prime}
= {4, 7, 15, 21, 45, 75, 105}.
```

The bound is 17,592,186,044,416. This formalizes the known
Mientka–Weitzenkamp (1969) result; it does not settle the unrestricted
problem, improve the known numerical bound, or claim a first formalization.
[OEIS A039669](https://oeis.org/A039669) already reports no further terms below
2^120, attributed to Max Alekseyev in 2011. Award eligibility is for the
organizer to assess.

## Proof

For each p in 3, 5, 11, 13, 19, 29, 37, explicit witnesses show that every
nonzero residue modulo p is a positive power of two with exponent at most
p-1. If a solution n exceeds 2^(p-1)+p, then p divides n: otherwise one of
the required primes n-2^k would have p as a proper divisor.
Combining these constraints gives the following exhaustive stages.

| Lower bound, exclusive | Upper bound, inclusive | Required divisor | Multiples checked |
| --- | --- | --- | --- |
| 21 | 1,035 | 15 | 68 |
| 1,035 | 4,109 | 165 | 18 |
| 4,109 | 262,163 | 2,145 | 121 |
| 262,163 | 268,435,485 | 40,755 | 6,580 |
| 268,435,485 | 68,719,476,773 | 1,181,895 | 57,916 |
| 68,719,476,773 | 17,592,186,044,416 | 43,730,115 | 400,718 |

There are 465,421 actual multiples in these stages. Balanced binary trees
also contain padding beyond each upper bound; `passes_sound` proves that
padding cannot establish a false result inside the interval. The range
n <= 21 and all seven positive examples are proved separately.

A table proposes an exponent and divisor for each candidate. The verifier
rechecks positivity, the congruence, and the strict proper-divisor bound.
Thus the table generator is not trusted. Closed certificate blocks contain
at most 1,024 evaluations and use `decide +kernel`; the blocks are joined by
a proved theorem, and their exact coverage is proved in Lean. No compiler
oracle, custom axiom, `sorry`, or `native_decide` occurs in the proof.

## Reproduce

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

Lean 4.34.0 and every dependency revision are pinned. The first script builds
with warnings as errors, replays `Main` with `leanchecker`, checks twelve
axiom closures and the fully expanded target type, verifies dependency
revisions, and rejects an invalid arithmetic statement. The second exports
the closures using pinned lean4export and checks them with pinned NaNoda,
allowing only `propext`, `Classical.choice`, and `Quot.sound`.
A successful contributor run is not an organizer decision. See the separate
submission evidence report for observed outcomes.

`python3 scripts/generate_certificates.py` deterministically regenerates
`Tables.lean`, `Certificate2.lean` through `Certificate7.lean`, and
`Certificates.lean` using only the Python standard library. It is optional
for verification: the committed Lean sources are the checked certificates.

See [STATEMENT.md](STATEMENT.md), [PROVENANCE.md](PROVENANCE.md), and
[NOTICE](NOTICE). Prepared for Ketian Zhang with OpenAI ChatGPT / Codex.

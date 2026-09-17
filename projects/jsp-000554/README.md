# JSP-000554: exact residue reduction for prime gaps without rough numbers

This Lean package formalizes an unconditional reduction and exact small-gap
classifications. It is **partial scope relative to JSP-000554 / Erdős 682**.
It does not prove the asymptotic estimate for exceptional prime gaps, the
density-zero conclusion, or the Hardy–Littlewood conditional asymptotic.
No mathematical novelty or first-formalization priority is claimed.

## Proven statements

`BadGap p h` asserts that `p` and `p+h` are prime, there is no prime strictly
between them, and every integer `m` strictly between them has `Nat.minFac m < h`.
Thus no interior integer has least prime factor at least the gap length.

Let `P(h)` be the product of all primes strictly less than `h`. Let `Omega(h)`
be the residues `b < P(h)` for which both endpoints `b,b+h` are coprime to
`P(h)`, while every `b+j`, `0<j<h`, is not coprime to `P(h)`.

For every natural `h >= 2` and every natural `p`,
`badGap_iff_residue_all` proves

```text
BadGap(p,h) iff
  h <= p and p is prime and p+h is prime and p mod P(h) belongs to Omega(h).
```

Endpoint primality is explicit; the residue table alone does not prove it.
Consecutivity is proved. Bertrand's postulate supplies the necessary bound
`h <= p`, accounting for small starting points.

`count_badGaps_all` proves the corresponding exact sum over residue classes
for any finite set of starting points, including any finite interval.
It does not assume a prime-pairs conjecture.

The following tables are proved by kernel reduction and connected to the
prime-gap predicate by the general theorem:

| Gap h | P(h) | Omega(h) |
| --- | --- | --- |
| 2 | 1 | empty |
| 4 | 6 | 1 |
| 6 | 30 | 1, 23 |
| 8 | 210 | 89, 113 |
| 10 | 210 | 1, 199 |
| 12 | 2310 | 1, 199, 467, 509, 1789, 1831, 2099, 2297 |

These classify arbitrarily large starting points, not experimental searches
up to a cutoff. Infinitely many prime pairs in these classes are not asserted.

## Source and attribution

The source is Ayla Gafni and Terence Tao,
[Rough numbers between consecutive primes, arXiv:2508.06463v1](https://arxiv.org/html/2508.06463v1),
Section 4: the definition of `Omega_h` and residue decomposition preceding
Conjecture 4.1. The full analytic result is their Theorem 1.1. Mathematical
credit remains with these authors and the cited earlier work. The tables
were independently computed from their definition.

This implementation was independently written with OpenAI ChatGPT assistance
under the submitting account's direction. Mathlib's primality, gcd,
finite-set and Bertrand-postulate infrastructure is acknowledged. No
contestant's proof or incomplete formal-conjectures statement is imported.

The [official catalog entry](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000554)
is interpreted using the precise research source. The original problem
concerns asymptotic frequency, not whether every prime gap contains a rough number.

## Reproduction

Lean and Mathlib: v4.34.0. Dependency commits: `lake-manifest.json`.
Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.

```bash
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first script builds with warnings treated as failures, runs the bundled
kernel checker, audits 12 targets against `propext`, `Classical.choice`,
`Quot.sound`, checks dependency revisions, rejects false arithmetic, and
cross-checks the tables in Python. Python is diagnostic; Lean proves the
unrestricted statements. The second exports the target dependency closures
for independent NaNoda checking. Actual outcomes belong in the verification
receipt; these instructions alone do not establish that a check passed.

The source uses `decide +kernel`. It has no `sorry`, `admit`, declared
mathematical axiom, `native_decide`, or compiler-trust proof shortcut.

## Submission status

This requests assessment of a partial formalization contribution. It is
not an announced award, approved claim, or promise of payment.
Recipient placeholder: `RECIPIENT-JSP-000554-KZ-A`, confirmation pending.
No private identity or payment details are included.

New proof and scripts: Apache-2.0. Documentation: CC BY 4.0, consistent with
the destination evidence repository.

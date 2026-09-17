# JSP-000212: finite Bose--Chowla lower-bound construction

For every prime `p` and every integer `h >= 2`, this package proves the existence
of a set `A` of exactly `p` positive integers, all at most `p^h - 1`, such that
two sums of `h` elements of `A` are equal only when their multisets of summands
are equal. Repeated summands are allowed. This is the classical `B_h` property.

The theorem `BoseChowla.jsp000212` takes `h=3` and proves the catalog's
distinct-three-element-subset condition. It is a **known lower-bound component**
of the open extremal problem, not a complete solution or an improved bound.
Only prime cardinalities are claimed here, not all prime powers. No asymptotic
limit for every interval length, matching upper bound, original mathematical
discovery, global first-formalization priority, or prize entitlement is claimed.

## Proof

Work in the degree-`h` finite extension of the field with `p` elements. Choose
an element `theta` whose minimal polynomial has degree `h`, and choose a
generator `g` of the multiplicative group. For every base-field element `a`,
`theta-a` is nonzero. Write it as `g^e(a)` with `0 <= e(a) < p^h-1`.
The exponents are distinct.

If two sums of `h` exponents agree, the corresponding products of `theta-a`
agree. Subtract the two monic products of linear polynomials. Their leading
terms cancel, giving a polynomial of degree below `h` that vanishes at
`theta`. The minimal-polynomial property forces it to be zero. Equality of
the multisets of roots then gives equality of the summands, including
multiplicities. Shift every exponent up by one to obtain positive integers.
Equal-cardinality sums preserve their equality under that shift.

The proof is universal; it does not enumerate a few primes or assume an
external finite-field computation. It imports Mathlib, not any unproved
conjecture theorem. The set definition uses actual multisets and actual sums.

## Source correspondence and attribution

- [Official JSP-000212 statement](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000212).
- R. C. Bose and S. Chowla, [Theorems in the additive theory of numbers](https://doi.org/10.1007/BF02566968), Commentarii Mathematici Helvetici 37 (1962/63), 141--147.
- Theorem 1 in the [authors' 1960 report](https://www.cs.umd.edu/~gasarch/COURSES/858/S13/BoseChowla.pdf) gives the classical construction, including its stronger modular and prime-power forms.
- [Formal Conjectures, Erdős 241](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/241.lean) discusses the related repeated-summand extremal function. Its asymptotic conjecture is not the theorem proved here, and that file is not imported or copied.

Mathematical credit belongs to Bose and Chowla. This Lean implementation was
written independently with OpenAI ChatGPT assistance under the direction of
the submitting account `ketianzhang1-lang`. Mathlib supplies finite fields,
primitive elements, cyclic multiplicative groups, and polynomial theory. The
new files are Apache-2.0; see `LICENSE`.

Bounded pre-submission searches on 2026-09-17 checked the official issues and
PRs for `JSP-000212`, `Bose`, `Chowla`, `241`, and `Sidon`, the submitting
account's proof branches, and the inspected plby proof-tree snapshot. No
matching submission was located. This does not establish worldwide priority.

## Reproduction

Lean 4.34.0 and all Git dependencies are locked. Mathlib is pinned to
`5ed2965256430c3649e86755f9576b54eca72435`.

```sh
lake exe cache get Mathlib.FieldTheory.Finite.GaloisField Mathlib.FieldTheory.PrimitiveElement Mathlib.Algebra.Polynomial.Roots Mathlib.Tactic
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

`Audit.lean` checks the final catalog-facing type, nonvacuous instances, and
five axiom closures. `verify.sh` builds with warnings as errors, replays the
compiled modules through the bundled Lean checker, audits all dependency
revisions, and requires rejection of false arithmetic. `verify_nanoda.sh`
uses pinned exporter/checker revisions and a strict allowlist of `propext`,
`Classical.choice`, and `Quot.sound`.

These commands specify the procedure. Successful-run receipts and source pins
are recorded separately in `VERIFICATION.md` after execution. Upstream compiled
caches are used; no full Mathlib source rebuild or independent human review
is claimed. Contribution eligibility and any award require organizer review.

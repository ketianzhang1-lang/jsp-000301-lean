# JSP-000295 / Erdos 357: the known square-root lower bound

This project proves, for every natural n,

`2 * Nat.sqrt n - 1 <= f n`.

Here f(n) is the maximum length of a strictly increasing integer sequence in
[1,n] for which all sums over different consecutive index intervals are distinct.
It also proves `2*sqrt(n)-3 <= f(n)` over the reals and the precise published
statement form `f(n) >= (2+o(1))*sqrt(n)`.

**Scope:** a complete formalization of this known lower-bound component.
It does not prove f(n)=o(n), determine the exact growth of f, or solve the
full JSP-000295 problem. The catalog currently labels that problem Progress.
No prize, first-formalization priority, or payment entitlement is asserted.

## Definitions and statement compatibility

`HasDistinctSums` quantifies over all order-connected finite index sets;
empty sets are included. `f` is the supremum of the admissible natural lengths.
The proof establishes that every admissible length is at most n before using
the supremum. Thus the lower bound does not exploit an unbounded-set convention.

`Compatibility.lean` reproduces the two mathematical definitions and the
Weisenberg theorem type from the following pinned Apache-2.0 source, omitting
only metadata attributes. It applies the new proof by definitional equality.
It imports no unproved upstream conjectures.

- [Formal Conjectures, Erdos 357, commit 40e7c98](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/357.lean)
- [Original problem and discussion](https://www.erdosproblems.com/forum/thread/357)
- [JSP-000295 catalog record](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000295)

## Elementary construction and proof

For every t>=0 take the 2t+1 consecutive integers

`t^2+1, t^2+2, ..., (t+1)^2`.

The sum of r consecutive terms starting at index u (zero based) is
`r*(2*t^2+1+2*u+r)/2`.
For fixed r this is strictly increasing in u. The smallest sum of r+1 terms
minus the largest sum of r terms equals `(t-r)^2+1`, which is positive.
Consequently sums from different lengths also cannot coincide. Every nonempty
sum is positive and therefore distinct from the empty sum.

For n>0 use t=Nat.sqrt(n)-1; the final term is at most n. The case n=0 is
handled separately. Taking the error function `o(n)=-3/sqrt(n)` yields the
stated asymptotic theorem, with the inequality required only eventually.

## Attribution and originality

The pinned Formal Conjectures statement attributes the asymptotic lower bound
to Desmond Weisenberg's comment. That mathematical credit is retained.
The proof implementation here was independently written with OpenAI ChatGPT
assistance. The two statement definitions and target type are adapted from the
Formal Conjectures Authors (2025), under Apache 2.0. Mathlib provides the
foundational arithmetic, finite-set, order and asymptotic infrastructure.

No mathematical discovery is claimed. A search of the official issue/PR text
for JSP-000295 and an inspection of the public plby/lean-proofs tree found no
same-scope submission or Erdos357 entry at the time of preparation. This is a
bounded search, not proof of worldwide priority; reviewers should assess overlap.

## Reproduction

Lean: `leanprover/lean4:v4.34.0`.
Mathlib: `5ed2965256430c3649e86755f9576b54eca72435` (v4.34.0).
All transitive dependencies are pinned in lake-manifest.json.

```sh
lake exe cache get Mathlib.Algebra.BigOperators.Intervals Mathlib.Order.Interval.Finset.Fin Mathlib.Data.Nat.Sqrt Mathlib.Analysis.Real.Sqrt Mathlib.Analysis.Asymptotics.Lemmas Mathlib.Analysis.SpecificLimits.Basic Mathlib.Tactic
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The workflow compiles all three modules with warnings treated as errors,
replays each using bundled leanchecker, audits nine targets against the
allowlist {propext, Classical.choice, Quot.sound}, checks dependency revisions,
rejects a false arithmetic negative control, and uses pinned lean4export and
NaNoda to check the target dependency closures with a strict axiom allowlist.

Only actual completed logs establish which checks passed. Workflow definitions
alone are not evidence of success. Cached Mathlib is used; its whole source is
not rebuilt from scratch. Bundled leanchecker uses Lean's own kernel; NaNoda is
a separate implementation. These are contributor-run checks, not organizer
certification or independent human review. GitHub workflow artifacts have finite
retention; compact receipts should be retained with any review submission.

## License

Apache License 2.0; see LICENSE. Retain the attribution above when reusing code.

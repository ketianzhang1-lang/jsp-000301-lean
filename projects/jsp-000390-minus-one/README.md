# JSP-000390: the known k = -1 special case

## Scope

This project formalizes only the classical special case `k = -1` of Erdős 479
(JSP-000390). It does **not** solve the original universal question for every
integer `k != 1`, improve known number-theoretic bounds, or claim a prize or priority.

The explicit moduli are `n = 3^r`. The main induction proves the stronger statement
`3^(r+1) | 2^(3^r) + 1` over the integers. A separate bound proves there are solutions
larger than every natural number, hence infinitely many positive solutions.

Headline declaration: `JSP000390.minus_one_infinite`.
All meanings use Mathlib's standard `Int.ModEq`, integer divisibility, natural
exponentiation, and `Set.Infinite`; positivity is explicit in `Solutions`.
For a positive modulus, -1 denotes the same residue as n-1, not a negative remainder.

## Verification

Lean 4.34.0 and Mathlib v4.34.0, with every transitive Git revision committed.

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The scripts run a warnings-as-errors project build, bundled kernel replay, actual
axiom audits for all five target theorems, a deliberately false negative control,
and a second implementation (NaNoda) on all target dependency closures. NaNoda's
strict allowlist contains only `propext`, `Classical.choice`, and `Quot.sound`;
no compiler-trust or native-evaluation axiom is allowed. Exact checker revisions
and reconstruction commands are in the scripts. Verification status must be read
from the corresponding public CI run; this README alone is not a pass certificate.

CI uses official cached Mathlib dependencies and network access to fetch tools.
This is contributor-run evidence, not organizer verification, independent human
review, or a clean offline rebuild of all Mathlib.

## Mathematical and formalization attribution

The [official catalog](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000390)
credits reported special cases to Ronald Graham, Derrick Lehmer and Emma Lehmer,
and a public explanatory note to Quanyu Tang. The powers-of-three construction is
classical; no mathematical-discovery credit is requested.

Original full question: https://www.erdosproblems.com/479
Related mathematical literature: A. Kalmynin, *On Novák numbers*,
https://arxiv.org/abs/1611.00417 .

This Lean source was prepared with OpenAI ChatGPT assistance under the direction
of the submitting GitHub account. No separate human or official referee is asserted.
It does not import third-party conjecture axioms or another submitter's proof.
Mathlib and Lean retain their existing authorship and licenses.

Bounded prior-art screening on 2026-09-16 found no official issue or PR under
`JSP-000390` or a PR under `479`. This is not a global priority guarantee.
The existing public `rjwalters/lean-genius` Erdős 479 file proves the k=2 case and
explicitly says its k=-1 case is not formalized; that prior contribution is
acknowledged, not claimed here. Formal Conjectures supplies an unproved full-question
statement; it is not imported into this project.

Eligibility for a new formalization of this small, already-known special case
requires an explicit organizer decision. No prize amount, first-formalization
priority, full-solution status, recipient confirmation, or payment is asserted.

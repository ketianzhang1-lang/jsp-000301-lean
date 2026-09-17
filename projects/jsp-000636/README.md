# JSP-000636: the universal multiplicity-antichain upper bound

This package formalizes **Lemma 2.5** of Yixin He and Quanyu Tang,
*An Erdős–Trotter problem on antichains with multiplicity r on each occurring
level*, [arXiv:2602.09803v1](https://arxiv.org/html/2602.09803v1#S2).
Mathematical credit remains with the cited authors and the classical
Erdős–Trotter observation they explain. The Lean implementation was written
with OpenAI ChatGPT assistance.

## Exact scope

For all natural numbers n >= 4 and r >= 2, let F be a finite family of distinct
subsets of an n-element ground set. If F is an antichain under inclusion and
each occurring size is represented at least r times, then F has at most n-3
different sizes. This is `JSP000636.size_count_le`.

For the original convention of exactly r sets of each occurring size,
`JSP000636.exact_multiplicity_card_le` proves |F| <= r(n-3). It accepts Mathlib's
`IsAntichain` directly; a proved equivalence connects the internal predicate.
`card_eq_mul_size_count` supplies the counting identity linking these forms.
Kernel-checked examples establish sharpness at n=4, r=2 and show why n>=4
and r>=2 cannot simply be omitted.

This is a supporting theorem of
[JSP-000636](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000636),
not a determination of n₀(r), a new parameter estimate, or a solution of the
full original problem. In particular the paper's lower and upper estimates
for n₀(r), and its exact n₀(2) and n₀(3), are not proved here. No mathematical
discovery, global first-formalization priority, award eligibility or payment
entitlement is claimed.

## Definitions and proof structure

The ground type is `Fin n`; both sets and families use `Finset`, so repeated
copies cannot supply multiplicity. Inclusion is ordinary subset inclusion.
The empty family is allowed and satisfies the upper bound. Sizes are counted
by `F.image Finset.card`, so each size is counted once.

If singleton members occur, two of them exclude two ground elements from
every larger member. A member occupying the entire remaining ground set
would be the unique member of that size, contrary to multiplicity. Thus
all occurring sizes lie between 1 and n-3. Complementation handles the
co-singleton case and preserves the number of sizes. Otherwise all sizes
lie between 2 and n-2. Counting those intervals proves the bound.

## Reproduction

Lean and Mathlib are pinned to v4.34.0; `lake-manifest.json` records the exact
dependency commits. From this directory:

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first script builds with warnings as errors, runs Lean's bundled kernel
checker, audits every one of the 14 project theorems, checks dependency
revisions and requires a false-arithmetic control to be rejected. The second
uses a separately implemented checker, NaNoda, with an explicit three-axiom
allowlist. Scripts describe the procedure; they are not a claim that a run
has succeeded. Consult the actual evidence receipt for results and limits.

No `sorry`, new axiom, or native decision procedure is used. Small examples
use ordinary kernel-evaluated `decide`.

## Prior-art screening and review request

On 2026-09-17, a search of the official prize's issues and pull requests for
JSP-000636 found no matching submission. The inspected plby/lean-proofs
snapshot `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` did not contain an
Erdos776 module. These bounded checks do not establish global priority.
The authors' public repository contains their paper, Python searches and
finite witnesses; it is credited as prior mathematical work, not claimed
as our work or imported as a Lean proof.

If considered for review, this should be assessed as a **limited supporting
formalization contribution**. It does not itself improve a bound on the
original threshold. Please assess whether that contribution merits any
recognition under the current rules. Recipient placeholder, if required:
`RECIPIENT-JSP-000636-KZ-A`; confirmation pending.

Source license: Apache-2.0 (LICENSE.LEAN). Documentation: CC BY 4.0.

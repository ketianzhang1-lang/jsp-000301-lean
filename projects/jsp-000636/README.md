# JSP-000636: antichain multiplicity and explicit threshold bounds

This package formalizes known results and a pair-label variant of the
construction in Yixin He and Quanyu Tang, *An Erdős–Trotter problem on
antichains with multiplicity r on each occurring level*,
[arXiv:2602.09803v1](https://arxiv.org/html/2602.09803v1).
Mathematical credit remains with these authors and the classical
Erdős–Trotter observation. OpenAI ChatGPT assistance is disclosed.
This is not a claim of a new mathematical discovery.

## Certified statements

The ground set is `Fin n`, and families are finsets of finsets, so repeated
copies cannot supply multiplicity. `Antichain` is equivalent to Mathlib's
ordinary inclusion `IsAntichain`. `sizes F` counts distinct cardinalities.
`Multiplicity r F` requires at least r members of every occurring size;
`ExactMultiplicity r F` requires exactly r.

| Theorem | Statement |
| --- | --- |
| `size_count_le` | For n >= 4 and r >= 2, every admissible F has at most n-3 occurring sizes. |
| `critical_size_bound`, `extremal_critical_le` | For r >= 4, g(2r+2,r) <= 2r-2. |
| `attaining_family` | For r >= 2 and n >= 2r+4 floor(sqrt r)+8, an admissible F with n-3 occurring sizes exists. |
| `thin_to_exact` | For positive r, an at-least-r family has an exactly-r subfamily with the same occurring sizes. |
| `exact_attaining_family` | In the same large-n range, an exactly-r antichain with n-3 sizes and r(n-3) members exists. |
| `extremal_eventually_eq` | For r >= 2 and n >= 2r+4 floor(sqrt r)+8, g(n,r)=n-3. |
| `threshold_exists`, `leastThreshold_spec` | For every r >= 2, the least eventual-equality threshold exists and has its defining property. |
| `leastThreshold_bounds` | For r >= 4, 2r+2 <= n0(r) <= 2r+4 floor(sqrt r)+7. |

Here g is a finite maximum over **all** admissible families, including the
empty family. `IsThreshold r N` means g(n,r)=n-3 for every n>N.
`leastThreshold` uses `Nat.find` only after proving threshold existence.
`thin_to_exact` also connects the paper's at-least-r convention with the
original exactly-r convention for positive r.

This supplement adds **23 theorems**, for **61 total**. It fills the
existence and thinning gaps in the previous packet. It remains a partial
formalization for [JSP-000636](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000636):
the paper's sharper asymptotic logarithmic upper estimate, the exact
small-r thresholds, and a general determination of n0(r) are not proved
here. No global first-formalization priority, award eligibility or payment
entitlement is claimed. The official catalog currently says
`Eligible to claim: No`.

## Construction and attribution

`JSP000636.lean` gives the universal bound (He–Tang Lemma 2.5) and
boundary examples. `Lower.lean` gives the critical obstruction and the
lower bound of Theorem 1.4, using the common-star argument and a symmetric
middle-level count.

The new construction specializes the section 4 label method to labels
of size two. Put k=floor(n/2) and partition the ground set into
{a}, P, {u}, V and R, of sizes 1, r, 1, k-r and n-k-2 respectively.

- At size 2 use {a,p} for the r different p in P.
- At size 3 use {a,u,x} for r different x in R.
- For each size t from 4 to k, choose a distinct two-element label in V
  and r different (t-3)-element subsets of R, and adjoin a and the label.

Singleton tags in P, the tag {u}, and equal-sized distinct labels in V
prevent inclusion between different levels. Payload selection supplies
r distinct sets within each level. All sets contain a. Adding all their
complements preserves the antichain and covers every size from 2 to n-2.
The numerical hypothesis ensures enough labels and payloads. This gives
a transparent O(sqrt r) error term; it does **not** formalize the paper's
O(log r) construction or claim a new optimal estimate.

`Upper.lean` contains finite subset selection and the half-family/complement
argument. `Construction.lean` contains separated tags and the general
pair-label half-family. `Threshold.lean` proves the numerical capacity,
eventual equality and least-threshold bounds. `Thinning.lean` proves the
exact-multiplicity bridge and exact attaining families.

## Reproduction

Lean and Mathlib are pinned to v4.34.0; `lake-manifest.json` records exact
commits. From this directory:

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first script compiles all six modules with warnings as errors,
replays them with Lean's bundled kernel checker, audits all 61 theorems,
checks dependency revisions, and requires false arithmetic to be rejected.
The second exports the complete dependency closures of the principal
results for the separate NaNoda checker, with a strict allowlist of
`propext`, `Classical.choice`, and `Quot.sound`.

These are reproduction instructions; actual results are recorded in
`VERIFICATION.md` and the referenced CI run. No `sorry`, new axiom, or
native decision procedure is used. The mathematical construction is
existential, using classical finite selection; no executable search for
optimal examples is claimed.

This extends official [PR #382](https://github.com/TheJustinSunPrize/awards/pull/382)
and should be reviewed in that existing thread. Source license:
Apache-2.0 (`LICENSE.LEAN`); documentation: CC BY 4.0.

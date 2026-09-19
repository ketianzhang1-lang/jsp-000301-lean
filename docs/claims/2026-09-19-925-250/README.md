# JSP-000925 and JSP-000250: contribution evidence for review

Prepared on 2026-09-19 for the existing self-applications by `ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance. This supplement records source comparisons and evidence of reuse. It does not change a Lean proof or assert an award decision.

| Problem | Existing catalog PR | Existing self-application | Contribution to assess |
| --- | --- | --- | --- |
| JSP-000925 / Erdős 1114 | [#342](https://github.com/TheJustinSunPrize/awards/pull/342) | [#1585](https://github.com/TheJustinSunPrize/awards/issues/1585) | Strict phase convexity and gap comparisons; construction and interval uniqueness of derivative roots; integration and verification |
| JSP-000250 / Erdős 294 | [#354](https://github.com/TheJustinSunPrize/awards/pull/354) | [#1465](https://github.com/TheJustinSunPrize/awards/issues/1465) | Original prime-obstruction upper formalization, retained in the complete package and reused in another complete submission; exact model integration and verification |

## JSP-000925: exact difference from the credited prerequisite

Compare the [pinned prerequisite](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1114.lean) with the [selected strict supplement](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/7b545f0e021b06d434654b17881c11819f3ff1b7/projects/jsp-000925-strict/JSP000925Strict.lean).

| Aspect | Pinned prerequisite | Added formalization |
| --- | --- | --- |
| Outward gap comparison | `RightGapMonotone` concludes `≤` | `RightGapStrict` concludes `<` at every permitted index |
| Analytic strictness | Supplies the phase, derivative formulas and moment estimates | `strict_algebra`, `phase_second_positive` and `phase_strict_convex` establish the strict positivity and strict convexity used in `canonical_strict` |
| Central comparison | Earlier non-strict comparison and reflection | The `N = 2*(i+1)` branch in `canonical_strict` proves the strict comparison from the single central gap when applicable |
| Derivative-root selector | Terminal `erdos_1114` receives the selector and its interval/zero hypotheses | `interval_critical_exists` constructs the interval root via Rolle; `exists_unique_strict_gaps` returns a selector |
| Interval uniqueness | Supplies reciprocal-sum strict decrease/injectivity | `interval_critical_unique` applies that infrastructure to the actual affine polynomial derivative; the endpoint includes uniqueness |
| Translation, positive spacing and nonzero leading coefficient | Already covered | Retained; these are not claimed as newly extended scope |

The complete endpoint has only the roots, degree, nonzero-polynomial and positive-spacing hypotheses. With degree `N+1` and roots indexed `0,...,N`, it returns the derivative roots, interval membership, derivative-zero equations, interval uniqueness, strict outward comparisons and gap symmetry.

The index condition is `i+2<N` and `N≤2*(i+1)`. For odd `N`, the two central mirror gaps remain equal and are excluded from strict comparison. For even `N`, the single central gap is compared with its right neighbor. For `N=1,2`, existence and uniqueness remain substantive, while gap comparisons are empty. This preserves the [recorded statement correspondence](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/7b545f0e021b06d434654b17881c11819f3ff1b7/projects/jsp-000925-strict/STATEMENT.md).

[Issue #24](https://github.com/TheJustinSunPrize/awards/issues/24) independently records that the prior endpoint is non-strict and assumes the selector. [PR #1402](https://github.com/TheJustinSunPrize/awards/pull/1402) records the same prior source and disclaims authorship for its catalog editor. Neither record is an organizer decision about this supplement.

**Requested assessment:** evaluate the added proof steps and stronger endpoint as an attributed contribution within a complete submission. The existence of an earlier non-strict proof is acknowledged. Whether these additions qualify for recognition under the prize rules remains for the organizer; no global-first assertion is made.

Mathematical credit remains with Bálint and the cited literature. The prerequisite's Codex / GPT-5.6 Sol credits are retained. The [original provenance record](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/491ddda5bbaab48b4c2f4c5bff6b3b1f29ea1a58/projects/jsp-000925-strict/PROVENANCE.md) identifies the applicant's additions and the reused infrastructure.

## JSP-000250: independently documented reuse of the original upper proof

The separate complete submission [PR #802](https://github.com/TheJustinSunPrize/awards/pull/802), associated with claim [#803](https://github.com/TheJustinSunPrize/awards/issues/803), explicitly credits `ketianzhang1-lang` for the reused upper-bound development. Its immutable [SOURCES.md](https://github.com/peilinliu66-dev/jsp-000250-lean/blob/37b7e70db36ea5cff44ef8c50c591b5f409fd820/SOURCES.md) identifies both the original proof commit and the historical PR source.

The source comparison completed for this supplement establishes:

1. The [original upper proof](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/567770d9977669a0846c491d0822fda8dddf9011/projects/jsp-000250/JSP000250.lean), [historical PR packet](https://github.com/TheJustinSunPrize/awards/blob/b583ad8173e9a6eac6de5238077d4d76e27a09ce/docs/submissions/jsp-000250-kz/JSP000250.lean), and [upper module in our complete package](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/e2f4c737ad4c2c9d7f4dcbfd4214fd2f2c96c876/projects/jsp-000250/JSP000250.lean) are byte-identical: Git blob `bf5793caf6ceadce9328f7e798926c280fb6dc76`, 11,107 bytes.
2. The [other submission's reused module](https://github.com/peilinliu66-dev/jsp-000250-lean/blob/37b7e70db36ea5cff44ef8c50c591b5f409fd820/JSP250ExistingUpper.lean) matches that entire original source after CRLF-to-LF normalization and removal of its added 1,599-byte normalized attribution/license header. No proof-body difference remains under that precisely stated comparison.
3. Its [upper bridge](https://github.com/peilinliu66-dev/jsp-000250-lean/blob/37b7e70db36ea5cff44ef8c50c591b5f409fd820/JSP250UpperBridge.lean) directly invokes `JSP000250.firstException_upper_bound` and `JSP000250.firstException_isBigO`. This is actual theorem reuse, beyond a bibliographic mention.
4. Our own [complete endpoint](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/e2f4c737ad4c2c9d7f4dcbfd4214fd2f2c96c876/projects/jsp-000250/JSP000250Complete.lean) also derives its upper direction from the retained `firstException_upper_bound`.

The original eleven-theorem upper development includes denominator clearing, the prime obstruction, least-exception properties, the explicit upper estimate and the eventual Big-O result. Its contribution is identifiable separately from the imported lower proof. Our ten integration theorems establish the exact representation and least-exception correspondence, lower-range witnesses including denominators one and two, and the complete two-sided endpoint.

**Requested assessment:** when reconciling complete packages and overlapping claims, retain and assess the applicant's original upper formalization and its documented reuse. Assess our later integration separately, preserving the other applicant's own contributions and the upstream lower-proof credits. This requests contribution recognition, not another person's allocation or an assertion that our complete package was earliest.

The quantitative target is the two-sided eventual comparison in Liu–Sawhney [Theorem 1.6](https://arxiv.org/html/2404.07113v1). Our selected endpoint gives constants `1/1000000`, `128` and triple-logarithm exponent `20`; it does not claim an exact asymptotic equivalent. The stronger lower profile is imported from the credited source closure, not claimed as newly authored here. The [provenance record](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5e102c18cde266e4bd9e5bff01e44685fcc03ec7/projects/jsp-000250/PROVENANCE.md) preserves Erdős–Graham, Liu–Sawhney, plby/lean-proofs and dependency attribution.

## Dated records and proof-version binding

All times below are UTC. CI timestamps describe executed runs; PR creation timestamps describe GitHub records. They do not prove the exact first public availability of every file or global priority.

| Record | Timestamp | Scope |
| --- | --- | --- |
| [925 verification run 35168402594](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168402594) | Created 2026-09-17 00:54:01; successful record updated 00:58:54 | Selected strict endpoint at `7b545f0e021b06d434654b17881c11819f3ff1b7` |
| [PR #342](https://github.com/TheJustinSunPrize/awards/pull/342) created | 2026-09-17 01:07:13 | Strict supplement; its historical source is byte-identical to the selected source |
| [250 original verification run 35168833566](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168833566) | Created 2026-09-17 01:00:25; successful record updated 01:03:59 | Original upper proof only, at `567770d9977669a0846c491d0822fda8dddf9011` |
| [PR #354](https://github.com/TheJustinSunPrize/awards/pull/354) created | 2026-09-17 01:13:41 | Initially upper-only; the complete package was added later |
| [PR #802](https://github.com/TheJustinSunPrize/awards/pull/802) created | 2026-09-17 15:37:17 | Separate complete submission crediting the original upper development |
| [250 complete verification run 35362198703](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35362198703) | Created 2026-09-18 15:24:13; successful record updated 15:38:41 | Complete package at `e2f4c737ad4c2c9d7f4dcbfd4214fd2f2c96c876` |

The complete 250 package is not backdated to the earlier upper-only submission. Prior complete upstream work, including the source registered in [PR #1265](https://github.com/TheJustinSunPrize/awards/pull/1265), remains relevant regardless of whether its contributors filed an award claim.

The selected 925 source and its [historical PR packet](https://github.com/TheJustinSunPrize/awards/blob/a6402918bd8c3ebd54b31325040fdfd86af1b267/docs/submissions/jsp-000925-strict-kz/JSP000925Strict.lean) have Git blob `691d469fec60fb5d5ded2d24a7d4e36073e84b19`, 11,436 bytes.

## Verification and review boundaries

The exact selected proof runs were rechecked as successful during this review. The existing receipts report eight axiom audits and 50,927 NaNoda declarations for [925](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/491ddda5bbaab48b4c2f4c5bff6b3b1f29ea1a58/projects/jsp-000925-strict/VERIFICATION.md), and 78 compiled modules, 21 axiom audits and 75,850 NaNoda declarations for [250](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5e102c18cde266e4bd9e5bff01e44685fcc03ec7/projects/jsp-000250/VERIFICATION.md). Both report only `propext`, `Classical.choice` and `Quot.sound` in audited closures.

This review performed source comparisons and checked those existing execution records; it did not rerun Lean or obtain independent human certification. The source-binding checks are reproducible with:

```sh
python3 verify_source_bindings.py
```

[sources.json](sources.json) records all ten immutable URLs, byte counts, SHA-256 values, Git blob IDs and comparison results. [verify_source_bindings.py](verify_source_bindings.py) verifies those bytes and the stated reuse comparison without executing downloaded source code. It does not validate Lean semantics or award eligibility.

Both existing self-applications and their catalog PRs remained open and unapproved when inspected. Please reconcile their complete-proof references, attributable contributions and overlapping claims, then complete account-to-contributor and eligibility review. This applicant-side evidence supports that review; it does not itself verify identity, establish payment entitlement or announce an award.

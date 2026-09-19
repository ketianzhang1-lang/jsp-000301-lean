# Updated lean-verify self-check: JSP-000925 and JSP-000250

**Overall conclusion: Verification passed for both exact submissions in the stated original-problem scope.** JSP-000925 completely formalizes strict outward derivative-root gap monotonicity, with existence, uniqueness and the required symmetry exception. JSP-000250 completely formalizes the eventual two-sided unit-fraction estimate, including its exact sequence and least-exception meaning. Statement review, unchanged-source reproduction, all 32 targets, kernel replay and independent checking succeeded. This satisfies the mathematical/Lean completeness requirements; procedural prerequisites for official acceptance remain pending as detailed below.

Prepared 2026-09-19 UTC. This contributor-commissioned self-check follows the [official skill fixed at awards commit 38e63c424c7196f8d4ceb664c5c25f0c0529d5e2](https://github.com/TheJustinSunPrize/awards/tree/38e63c424c7196f8d4ceb664c5c25f0c0529d5e2/skills/lean-verify). Public submission materials are in English. This is not certification by an independent human referee or an award decision.

## Required judgments

| Question | JSP-000925 | JSP-000250 |
|---|---|---|
| Does the statement express the specified original problem? | Yes: strict outward derivative-root gaps with the symmetry exception | Yes: the least forbidden initial denominator and the complete eventual two-sided estimate |
| Has this exact proof commit actually passed the checks? | Yes: 9/9 targets passed at the selected commit | Yes: 23/23 targets passed at the selected commit |
| Does it completely solve the specified problem? | Yes, all stated gap, symmetry and selector obligations | Yes, both bounds, exact model and all required cases |
| Does it meet the Lean completeness requirements? | Meets the requirements within the stated trust boundary | Meets the requirements within the stated trust boundary |

## Fixed inputs and source trace

| Item | JSP-000925 | JSP-000250 |
|---|---|---|
| Awards PR / existing claim | [342](https://github.com/TheJustinSunPrize/awards/pull/342) / [1585](https://github.com/TheJustinSunPrize/awards/issues/1585) | [354](https://github.com/TheJustinSunPrize/awards/pull/354) / [1465](https://github.com/TheJustinSunPrize/awards/issues/1465) |
| Awards PR head | `f9083a134b3e185ebbc6b94f59ac21819e93f755` | `45174adb114d9ebd8fffc5e3fe3314a93f56aed5` |
| Awards base | `TheJustinSunPrize/awards`, `main`, `ff33abd13163e789790eb1014e55f57c05f94432` | Same |
| Proof repository | `ketianzhang1-lang/jsp-000301-lean` | Same |
| Proof branch | `jsp-000925-strict-gaps` | `jsp-000250-prime-obstruction` |
| Exact proof commit | `7b545f0e021b06d434654b17881c11819f3ff1b7` | `e2f4c737ad4c2c9d7f4dcbfd4214fd2f2c96c876` |
| Project directory | `projects/jsp-000925-strict` | `projects/jsp-000250` |
| Complete endpoint | `JSP000925Strict.exists_unique_strict_gaps` | `JSP000250.jsp_000250`; `JSP000250.liu_sawhney_resolution` |

The awards head repository for both is `ketianzhang1-lang/awards`; the respective branches are `jsp-000925-strict-evidence` and `jsp-000250-upper-bound-evidence`. Timestamped API metadata are retained in `evidence/submission-snapshot.json`. The PRs each contain one catalog-file change and three commits. Full file lists, commits, review, inline-comment and ordinary-comment collections were read; the latter three collections were empty. Base/head catalog comparison shows changes only to Lean proof information and attribution, without narrowing the original question or changing mathematical status or eligibility. Both proof commits exist and were checked out exactly; the execution artifacts also record ancestry against their named branch tips. Proof commits, awards PR commits, harness commit and report commit are separate identifiers. Later documentation revisions `491ddda5bbaab48b4c2f4c5bff6b3b1f29ea1a58` and `5e102c18cde266e4bd9e5bff01e44685fcc03ec7` are evidence-only references, not replacement proof versions.

## Original statements and complete coverage

### JSP-000925 / Erdős 1114

Primary literature: L. Lorch, *Some monotonicity properties of polynomials with equally spaced zeros*, Acta Mathematica Academiae Scientiarum Hungaricae 27 (1976), 293-300, [publisher record](https://link.springer.com/article/10.1007/BF01902106), [public volume](https://real-j.mtak.hu/7424/1/MTA_ActaMathHung_27.pdf). Printed page 293 (PDF page 307) was inspected visually as well as by text extraction. Its introduction attributes the outward derivative-gap result to Erdős and Bálint; it treats simple, exclusively real, equally spaced roots and explains reduction by scaling and symmetry. The cited Bálint paper itself was not inspected. Direct access to erdosproblems.com was blocked (HTTP 403); the attempted independently pinned Formal Conjectures 1114 file did not exist at that revision. Neither failed source is represented as read. The original catalog, this primary literature and the explicit polynomial statement supply the correspondence evidence.

For a nonzero real polynomial of degree `N+1`, with `N>0`, all roots `a+d*j` (`0≤j≤N`) and arbitrary `d>0`, the endpoint constructs a unique derivative zero in every adjacent-root interval. These are N distinct ordered zeros. Since the derivative has degree N, they exhaust its zeros; no additional critical points are omitted by the interval representation. Arbitrary translation and nonzero leading coefficient are permitted. The polynomial factorization follows from its degree and N+1 distinct roots, rather than assuming the desired derivative behavior.

| Original obligation | Lean targets / definitions | Evidence and remaining gap |
|---|---|---|
| Actual polynomial, all simple equally spaced roots, arbitrary scale | `strict_gap_theorem`, `exists_unique_strict_gaps`, upstream `eq_progression_factorization` | Uses `Polynomial.eval` and `Polynomial.derivative`; degree and root family are explicit. No semantic gap found. |
| Derivative zeros exist and are unique in each interval | `interval_critical_exists`, `interval_critical_unique`, complete endpoint | Rolle's theorem constructs them; strict decrease of the normalized reciprocal sum gives uniqueness. Endpoint assumes no selector. |
| Strict outward right-side gaps | `strict_algebra`, `phase_second_positive`, `phase_strict_convex`, `canonical_strict`, `strict_gap_theorem` | The strict convexity ingredient is proved. The index range is exactly `i+2<N` and `N≤2*(i+1)`. |
| Reflection and left-side gaps | `GapSymmetric`, complete endpoint | Equality of mirror gaps transfers the right-side comparison to the left. Natural subtraction is safe under the explicit index bounds. |
| Central and small-degree cases | Complete endpoint and `Verify925.intended` | N even: the single central gap is compared outward. N odd: the two central mirror gaps are equal and are excluded from strict comparison. N=1,2 have existence/uniqueness and no required gap comparison. Degree one has no derivative-root gaps and is vacuous. |
| Independently exposed conclusion | `Verify925.intended` in `bridge925.lean` | Restates interval inequalities, derivative evaluation, uniqueness, strict gaps and mirror equality explicitly, then derives them from the submitted endpoint. |

`b` is a total natural-indexed function, but only indices below N carry root meaning. Its unconstrained values beyond N never enter the claimed comparisons. The strict theorem does not claim global strict increase from left to right; it states increase outward from the center, respecting equal mirror pairs.

The upstream analytic development is fetched from `plby/lean-proofs` at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, `src/latest/ErdosProblems/Erdos1114.lean`, SHA-256 `570e485a1548dd090451dc095ed1ed1128806631e1abff4893405f3e42ea1825`. It is credited to its upstream authors, including Codex/GPT-5.6 Sol, with the mathematics credited separately. The applicant claims the strictness, selector construction/uniqueness and verification contribution, not authorship of the imported non-strict development or new informal mathematics.

### JSP-000250 / Erdős 294

Primary source: [Liu and Sawhney, arXiv:2404.07113v1, Theorem 1.6](https://arxiv.org/html/2404.07113v1#S1.Thmtheorem6). The source defines the smallest positive initial denominator with no increasing unit-fraction representation under cutoff N and gives an eventual two-sided comparison. It is not an exact asymptotic equivalent or a bound required for every small N. Its lower triple-logarithm exponent is an unspecified constant; the submitted development supplies explicit constants and exponent.

The inspected model is a finite set of distinct positive natural denominators, containing its least member t, with every denominator at most N and rational reciprocal sum exactly one. `firstException` uses `Nat.find` on a proved nonempty set of positive failures (N+1 is a witness); it cannot exploit a default value for an empty infimum. The sequence equivalence uses an order isomorphism of a nonempty finite set in one direction and the injective image of a strictly increasing sequence in the other. Positivity of the first element implies positivity of every denominator.

| Original obligation | Lean targets / definitions | Evidence and remaining gap |
|---|---|---|
| Exact finite increasing positive sequence and reciprocal sum | `representable_iff_upstream`, `representable_iff_increasing_sequence`, `Verify250.sequence_iff` | Strict monotonicity enforces distinctness; literal rational reciprocal sum and cutoff. No semantic gap found. |
| Least positive failure, including cutoff zero | `exists_exception`, `firstException_spec`, `firstException_le`, `smaller_denominators_representable`, `firstException_eq_firstForbidden` | Existence, nonrepresentation, positivity and minimality are proved, with no asymptotic premise needed. |
| Unconditional upper estimate | Eleven original `JSP000250` targets and `eventually_explicit_upper_bound` | Denominator clearing, prime obstruction and LCM estimates give eventual `t(N)≤128*N/log N`. |
| Unconditional lower estimate and witnesses | `eventually_all_small_denominators_representable`, sequence witness theorem, `eventually_strict_lower_bound` | Pinned 75-module closure proves the analytic ingredients; no Fourier, density or representation hypothesis is left in the endpoint. Cases t=1 and t=2 are supplied using {1} and {2,3,6}; all t≥3 use the imported theorem. |
| Complete two-sided estimate | `jsp_000250`, `liu_sawhney_resolution`, `Verify250.intended` | Eventually `(1/1000000)*N/(log N*(log log N)^3*(log log log N)^20) < t(N) ≤128*N/log N`; positive constants and exponent 20 witness the source formulation. |

The independent bridge uses an explicit sequence definition and combines nonrepresentation, all-smaller-positive representation and the literal two-sided inequality in one theorem. It does not merely rename `firstException` or assume its intended meaning. The eventual threshold remains existential, as permitted by the source.

The lower formalization and all 75 transitive source modules are pinned to the same upstream commit above. `UPSTREAM.json` records original hashes, ported hashes and precise compatibility edits. Bootstrap checks both original and ported bytes. The `UnitFractions` and `PrimeNumberTheoremAnd` libraries and all preserved notices remain attributed. The applicant's eleven original upper theorems are retained; ten integration theorems connect the models, lower witnesses and combined result. The imported lower proof is not claimed as the applicant's work.

## Execution protocol and trust boundary

The harness is separate from the selected proof commits. Each proof checkout is unchanged; added audit bridges appear only in the disposable copies after the original clean build. The workflow fixes Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`, all nine manifest revisions, lean4export `6cea97789dc088ea47fcea15692db85685aedac5`, and NaNoda `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.

Dependencies and checksum-verified bootstrap inputs are downloaded first. Verification runs offline in a disposable non-root Docker container, UID 10001, all capabilities dropped, no-new-privileges, two CPUs, 6 GiB memory and a 512-process limit. No account credentials are mounted. Only disposable proof and evidence directories are writable; the harness is read-only.

Project outputs are removed before `lake build --wfail` and the original verifier. For 250, the default Lake target alone is insufficient: the submitted complete verifier explicitly recompiles all 78 project/closure modules with warnings as errors, including `JSP000250Complete` and `AuditComplete`, without a resume option. The official target audit then explicitly builds and checks every target's module and source. Every target and bridge receives `#check`, full `#print`, and transitive `#print axioms`. Submitted proof modules and audit bridges receive Lean kernel replay, followed by independent NaNoda checking of the exported target dependency closures, with a hard-error allowlist of only `propext`, `Classical.choice`, and `Quot.sound`. The original verifier also rejects a false-arithmetic negative control.

Actual dependency Git revisions and before/after input hashes are compared. Original/ported upstream hashes, exact commands, exits, durations, source trace and full logs are retained. The official preflight reports checker compatibility as not probed because that helper does not test external tools; successful separate kernel and NaNoda execution must discharge that prerequisite. Its manual preconditions are checked against container settings, tool versions, dependencies, source hashes and module mappings. The automatic manifest's `coverage: pending` fields are preserved as executed: automation does not make semantic judgments. Separate reviewed manifests record the coverage conclusions above.

Trusted Mathlib dependency caches are retained: this is a clean rebuild of the submitted project and bootstrapped local proof closure, not a rebuild of the entire compiler or all Mathlib. Independent checking does not remove trust in checker implementations, toolchain distribution, hardware or source acquisition. The bridges independently restate the intended objects but import the submitted proof environment; they are not a separately compiled clean-room comparator. Natural-language correspondence remains a mathematical review. Static source scans are only locators and never replace the transitive axiom results.

## Fresh execution results

The fresh [workflow 35455281765](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35455281765) succeeded at harness commit `651a8f084da280d8c388c6f95f6392b310f77084`. Downloaded artifact ZIP digests and every internal file hash were independently verified. All required verification stages exited zero; negative controls produced their expected rejection.

| Problem | Targets | Original complete verifier | Official per-target audit | Independent NaNoda result |
|---|---:|---:|---:|---|
| 925 | 9 | 49.07 s | 174.87 s | Checked 50929 declarations with no errors |
| 250 | 23 | 1508.99 s | 1165.63 s | Checked 75855 declarations with no errors |

Every target and audit bridge had exactly `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. No placeholder or native-computation axiom was observed. All nine actual dependency revisions matched their manifest pins. Source input hashes were unchanged. Only the separately identified bridges were added to the disposable checkouts. Both negative controls failed for the intended false proposition `1 = 0`, rather than a missing import or tool failure. The 250 complete verifier freshly compiled all 78 modules and replayed all five project prefixes. Original module replay, bridge replay, export and independent NaNoda checking all succeeded.

The raw artifacts include the fetched source snapshots needed to identify exactly what was checked; this does not change their upstream authorship or license notices. The proof submission itself continues to fetch its pinned upstream inputs through bootstrap. The primary literature PDF is not redistributed in this bundle. Execution paths `/out/...` map to `evidence/<problem>/remote/...` in the preserved bundle.

## Official prerequisites and attribution review

A successful Lean completeness audit does not establish candidate registration, identity, priority, merged status or award entitlement. These existing PRs predate this supplemental check. Their literal pre-opening self-check declarations must remain unchecked; no date is backdated. Maintainers must decide how that timing requirement applies to an existing PR.

The official candidate register at the fixed rules revision has no structured candidate records. Other intake discussions exist; absence of a structured record does not mean no one has contacted the organizers. Mathematical review and solver registration must precede registration of a Lean candidate. No accepted solver record is supplied for either submission. Both PRs are currently open and unmerged, so the merged-PR declarations in their existing claims remain unchecked. These Lean-only claims do not assert the solver-awaiting-formalization exception.

For 925, issue #24 and PR #1402 document the pre-existing upstream formalization; the latter recorder disclaims authorship and award entitlement. For 250, PR #802 / claim #803 present another applicant's complete package and explicitly credit this applicant's reused upper proof. PR #1265 records the upstream proof and disclaims recorder authorship. The current contribution must be assessed alongside those records, without claiming first-formalization priority, exclusivity or another contributor's work.

Official repository write access previously returned HTTP 403. Replacement PR and claim texts are supplied for copying into the existing threads; this report does not imply they have been applied online.


See `target-index.md` for commit-fixed declaration locations, `axiom-results.md` for complete per-target axiom lists, `evidence/execution-summary.json` for actual commands/durations/dependencies, and `how-to-reproduce.md` for reproduction guidance. Full artifact digests and internal hashes are verified after download.


The final metadata recheck confirmed the two awards heads and the official rules commit remained unchanged, and both PRs remained unmerged. Report finalized 2026-09-19T17:25:13+00:00.

# JSP-000393 / Erdős 485: semantic review and coefficient-domain completion

**Status: the original rational-only commit does not establish the full historical coefficient domain. A new characteristic-zero-field completion has been prepared at `aa1ed1bac2eb0c1ec33723ff802ff3b9b6c02ee8`; actual verification of that new commit remains pending in this review.** The new statement includes complex coefficients, and static review found a complete route through the already-proved generic upstream algebraic lemmas. Mechanical success must be filled in from the new commit's isolated run, not copied from any historical result.

| Required judgment | Original `17e40659…` | New `aa1ed1ba…` at this review stage |
| --- | --- | --- |
| Does the formalized object match the full original problem? | No: only rational/integer coefficients are covered. | Yes in static statement review: all complex polynomials are included literally; the generic theorem covers characteristic-zero fields. |
| Has this exact commit actually passed fresh verification? | Not determined by this semantic review. Historical results are separate. | Pending isolated build, all target/bridge audits, kernel replay and external checker. |
| Does it completely solve the original problem? | No full-domain resolution is established by that commit. | Pending actual checks; the stated proof route and coverage are complete. |
| Does it satisfy the Lean completeness requirements? | No, if assessed as a complete original-domain submission. | Not yet established; do not preannounce a pass. |

## Fixed inputs

- Awards [PR #368](https://github.com/TheJustinSunPrize/awards/pull/368), base `ff33abd13163e789790eb1014e55f57c05f94432`, head `e7850f739564ea77ccb8e7b3832c5ea5d4be3eba`, contributor branch `jsp-000393-sparse-squares-evidence`.
- [Claim #1479](https://github.com/TheJustinSunPrize/awards/issues/1479). PR metadata reports six commits and one changed file; all six commits and the complete one-file response were fetched. Ordinary PR comments, review comments, reviews, and claim comments were each empty at retrieval. Raw snapshot and retrieval timestamp: `github-snapshot.json`.
- The PR only changes Lean proof and Attribution basis in the JSP-000393 entry. Its base/head descriptions remain the same broad question about nonzero terms of a polynomial and its square. The base bibliography directly cites Schinzel (1987); it does not restrict coefficients to the rationals. Exact entry snapshots: `catalog-base-entry.md`, `catalog-head-entry.md`.
- Original construction priority anchor: `a337720331a34599114a9d4669d6518d5e608f6f`. Original complete *rational* integration: `17e406594d644b40c9a742e843cd6d89f319c872`, proof repository `ketianzhang1-lang/jsp-000301-lean`, branch `jsp-000393-sparse-squares`, project root `.`.
- Later historical verification-only revision: `0e86d155839b409faa075233a1b62e32f2b7b1e3`. Its NaNoda evidence must not be represented as an execution at the original proof commit.
- New coefficient-domain completion: [proof commit `aa1ed1bac2eb0c1ec33723ff802ff3b9b6c02ee8`](https://github.com/ketianzhang1-lang/jsp-000301-lean/commit/aa1ed1bac2eb0c1ec33723ff802ff3b9b6c02ee8), branch `jsp-000393-general-coefficients`. The parent agent created this commit from the new candidate files. The new commit must independently pass all required checks and remain explicitly distinguished from original-priority anchors.

## Original-source scope: decisive correction

The opening paragraph on printed p.55 of [Schinzel's 1987 primary paper](https://matwbn.icm.edu.pl/ksiazki/aa/aa49/aa4916.pdf) specifies complex coefficients for the historical minimum-square-support question. Its general theorem covers characteristic-zero fields. This was confirmed by visually reading the scanned first page, not inferred from a search snippet.

Problem 4.4 on printed p.73 of the [Hayman–Lingham 2018 edition](https://arxiv.org/abs/1809.07200v2) asks for a uniform threshold: sufficiently many terms in a polynomial force sufficiently many terms in its square. This is equivalent to divergence of the minimum over exact support sizes. The modern compilation was consulted directly; the separately cited 1974 publication was not independently obtained.

The [fixed Formal Conjectures reference](https://github.com/google-deepmind/formal-conjectures/blob/5657b3b9ae1c174fdbab9d9d600b018238ba573c/FormalConjectures/ErdosProblems/485.lean) instead explicitly uses `ℚ[X]`. That file contains an unfilled target and is not imported by this proof. It provides a precise comparison statement, but is neither an organizer-approved challenge nor justification for silently narrowing the primary problem. The direct Erdős 485 webpage returned HTTP 403; no browser fallback or substitute problem was used.

The old endpoint over the rationals cannot alone establish the complex minimum lower bound: minimizing over the larger complex domain can only make the minimum smaller. An injective rational-to-complex map supplies examples and upper bounds, not the missing lower bound. The newly added generic induction repairs this logical gap directly.

The exact 13-term seed and its 12-term square match the example on printed p.86 of [Coppersmith–Davenport (1991)](https://matwbn.icm.edu.pl/ksiazki/aa/aa58/aa5816.pdf). That source uses real coefficients in its introductory minimum formulation; the characteristic-zero-field completion encompasses real, complex, rational, and integer-derived cases. Only squares are claimed here; the paper's arbitrary-power results and optimal/all-size quantitative estimates are outside this submission.

Source URLs, exact page locations, downloaded-file hashes and access limitations are recorded in `primary-source-record.json`. Copyrighted complete PDFs/page images are reviewer scratch, not deliverable evidence attachments.

## Definitions, requirements, and coverage matrix

Let `T(P) = P.support.card`. The independently specified minimum is `sInf {m : ℕ | ∃ P : K[X], T(P)=k ∧ T(P^2)=m}`. For the historical source, take `K=ℂ`. The theorem `minimum_attained` ensures this natural infimum is achieved by a real polynomial object in the designated coefficient field, including at `k=0`; it is not the default infimum of an empty set.

| Requirement | Original/local declaration | New completion and independent bridge | Static assessment |
| --- | --- | --- | --- |
| Actual support of the polynomial and its square | `Erdos485.termCount`, `squareTermCounts`, `f` in upstream Basic; `integer_support` | `JSP000393General.minimumSquareTerms`; `Verify393General.minimum_definition` uses literal `ℂ[X]`, `Polynomial.support` and `sInf` | Exact semantics; no substitute support statistic or restricted coefficient family. |
| Every support size has an admissible polynomial; the minimum is attained | `Erdos485.f_attained`, `f_minimal` | `minimum_attained`, `minimum_le`; `complex_attained`, `complex_zero_and_one` | Rational examples are injected into K only to prove nonemptiness. The minimum still ranges over all K-polynomials. Zero and one cases explicitly audited. |
| Uniform lower estimate, arbitrary complex coefficients and degree | Original endpoint only `ℚ[X]`; generic algebraic infrastructure already present | `schinzel_support_bound`, `schinzel_term_bound`, `uniform_threshold`; `complex_uniform_threshold` | General induction over square-support count discharges every reduction, with no rational-only lower theorem in the chain. |
| Minimum diverges for all large k | `Erdos485.erdos_485`, `JSP000393Complete.minimum_diverges` only rational | `minimum_diverges`, literal `complex_original`; `Verify393General.intended` | For every B use cutoff `2 + 32^(2^B)` and an attained minimizer. Uniform over all polynomial coefficients/degrees. |
| For every natural k, an actual family has support sizes `13^k`, `12^k` | `JSP000393.family_counts`, `rational_family_counts` | `JSP000393General.family_counts` | The seed is exact, not numerical evidence. Base-25 exponent separation avoids collisions both before and after squaring. k=0 is the constant polynomial. |
| The genuine minimum satisfies `f(13^k) ≤ 12^k` | `JSP000393Complete.minimum_family_upper_bound` | General `minimum_family_upper_bound`; combined independent bridge | Follows from an actual admissible polynomial and the minimum property, not a renamed family statistic. |
| For all M and all cutoffs N, some n≥N has `M*f(n)<n` | `arbitrarily_large_small_ratio` | General same-name theorem and combined bridge | Quantifier order includes both independent parameters. Witness `13^(12*(M+N+1))`; no assertion for every support size. |
| Integer-polynomial explicit threshold and old contribution preserved | `integer_schinzel_bound`, `integer_uniform_threshold` | Original sources remain in the combined audit target list | Both old targets remain independently checked; no generic-field extension is backdated. |

`target-index.json` lists the source coordinates for every original target, new generic target, and independent complex bridge. The new general-module index uses the final selected source hash `1a017d44477daf23cadf1d39a9297c73258dc888070b962749fe7313cd5e6b08`, including the GitHub-handle attribution and scoped `omit` repair. Actual checked-commit hashes from CI must agree.

## Lower-bound proof chain and absence of a hidden hypothesis

The upstream `Schinzel.lean` contains conditional helper theorems, so finding a compile-successful helper would not suffice. In the original rational endpoint the conditions are actually discharged by `primitiveTrinomialProperty`, `deformationRecursiveProperty`, `primitiveSchinzelInductionStep`, and `schinzel_reduction`. Its limitation is the field of coefficients, not an assumed lower bound.

For the new arbitrary-field wrapper, the directly used lower lemmas were individually checked against their actual signatures:

1. `three_le_sq_support_card` and `exists_primitiveNormalization` hold over `[Field K] [CharZero K]`.
2. `primitive_trinomial_support_card_eq_two` has a general-field theorem which proves the necessary algebraic-closure transport internally.
3. `primitiveNormalization_deformation` gives the small-support estimate or an actual `Deformation` for the normalized polynomial.
4. `Deformation.exists_eq_scalar_mul_sq` supplies a nonzero scalar and actual bivariate square, using the fully proved squarefree-gap/coprimality chain.
5. `deformation_recursive_step_of_scalar_square` produces a polynomial in the same field with strictly fewer square-support terms and the required original-support comparison.
6. Strong induction and `B_mono`/`B_pred_sq_lt` finish the bound for the original polynomial. No existential field extension is substituted for the required same-field recursive polynomial.

The new candidate received a second static review by the parallel reviewer of JSP-000912. That reviewer confirmed the general signatures and the nonempty-minimum argument. This is assistant-assisted review, not independent human certification.

All 22 upstream source inputs were fetched by the statically reviewed bootstrap script. Every resulting port hash matches `UPSTREAM.json`; only five files have documented mechanical compatibility changes. No upstream mathematical lemma was altered for the generic completion. The 24 original proof files' keyword scan found none of the selected placeholder/native-evaluation/kernel-bypass patterns; `static-scan.json` is only navigation evidence, not a substitute for the required transitive axiom and external checks.

## First general-field candidate and verification repair

The first 2026-09-19 general-field candidate `ed82d0cb2d35fca55f32b00cb75bdd5271226eb8` failed its warnings-as-errors check because `minimum_le` retained an unused automatic `CharZero` section parameter. The selected `aa1ed1bac2eb0c1ec33723ff802ff3b9b6c02ee8` adds `omit [CharZero K] in` for that lemma and updates its checksum; the mathematical proof is unchanged. The first candidate is historical evidence, not a selected passing version. The selected revision requires its own completed full self-check. The original complete verifier passed during the first run; the new general module was stopped by the linter-as-error gate. This is not a mathematical counterexample and is not a successful audit of either generic candidate. No linter was disabled. The final candidate was published at 2026-09-19T23:48:04Z.

## Engineering and exact-version checks still required

- Toolchain: `leanprover/lean4:v4.34.0`; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`; nine manifest-pinned dependencies. Do not run `lake update`.
- Original clean verifier: `python3 scripts/verify_complete.py`; it compiles 22 upstream + 2 original local proof + 1 audit modules, validates 13 original target axiom reports, checks manifest SHAs, replays kernel targets and runs a false-arithmetic control.
- New verifier: `python3 scripts/verify_general.py`; it first invokes that unchanged original complete verifier, then checks the general-field module and `AuditGeneral` (27 compiled modules total; 13 old + 11 new original reports). Output directory: `evidence-general`, with the original nested evidence in `evidence-complete`.
- The original Lake file already includes the rational complete/audit roots in default targets. The new Lake target includes both the generic theorem module and `AuditGeneral`; nevertheless the explicit verifier and official target audits remain necessary.
- `targetsGeneral.json` contains 29 actual targets: 13 original, 11 general-field, 5 independently specified complex bridges. The parent agent must set the real new proof SHA before invoking the official script. Three bootstrap-defined original theorems use tracked `AuditComplete.lean` as their verification entry; each entry records its actual `definition_source`, pinned URL and hash separately.
- Record the new proof's clean source state, tracked source hashes, bootstrap original/port hashes, dependency SHAs, all exact `#check`/`#print`/`#print axioms` outputs, bridge compilation, kernel closure, NaNoda export/config and negative control. Standard classical foundations permitted for this audit are `propext`, `Classical.choice`, and `Quot.sound`; additional dependencies cannot be silently accepted.
- Do not label a new run successful from historical receipts or a green unrelated PR check. This semantic-review process did not execute Lean/Lake or any submitted proof code on the local host.

## Attribution and related work

Mathematical credit remains with Schinzel for the lower bound and Coppersmith–Davenport for the sparse seed/construction context. The 22 upstream modules are attributed in their retained source/provenance to Codex / GPT-5.6 Sol at plby commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`; copyright/license notices and the mechanical port record remain.

The account `ketianzhang1-lang` claims its disclosed implementation of the explicit seed/product family, rational support/minimum integration, and now the general-field induction/minimum interface, with ChatGPT/Codex assistance. The new wrapper reuses the existing general-field algebraic proof. It is not an independently discovered mathematical proof or a new implementation of those upstream algebraic lemmas. Repository ownership alone does not verify identity or authorship.

[Issue #44](https://github.com/TheJustinSunPrize/awards/issues/44) registered the existing rational lower formalization before this integration and disclaims a new-proof/award claim for its recorder. [PR #1298](https://github.com/TheJustinSunPrize/awards/pull/1298), still open at retrieval, also records that existing proof and disclaims authorship/award eligibility. [PR #921](https://github.com/TheJustinSunPrize/awards/pull/921) is closed and unmerged; its disclosed 13/12 seed result overlaps the classical construction but does not itself establish the diverging minimum. Current related metadata is preserved in the review directory; no implication of official acceptance or priority adjudication is made.

## Required replacement-text changes

1. Lead with the new complex/general-coefficient completion and supply its **new** full proof SHA, branch and `JSP000393General.complex_original`/`jsp_000393` targets. Explicitly say the original rational commit lacked the broader coefficient-domain endpoint and retain it as history, not a second fully complete submission.
2. Explain that the minimum quantifies over all complex polynomials and is attained, and that the generic induction uses proved generic upstream reductions. Keep attribution, exact 13/12 counts, minimum upper bound, arbitrary-cutoff quantifiers and the scope exclusions.
3. Replace stale unexecuted-self-check prose only after the actual new-commit run completes. Include all 29 actual target outcomes and the precise four judgments, keeping any failure or resource blocker visible. Preserve historical receipts only in a clearly historical section.
4. Use fresh review/report/source links and real verification dates. Do not backdate the new domain completion, its execution, or the pre-PR timing checkbox.
5. Retain pending solver registration, organizer statement/math review, identity/attribution adjudication and PR merge declarations. A completed Lean verification alone cannot make those external procedural declarations true.

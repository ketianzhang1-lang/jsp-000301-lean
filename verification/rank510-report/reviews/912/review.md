# JSP-000912 / Erdős 1099 — semantic review and audit inputs

**Static review complete; execution remains pending in this sub-review.** The pinned proof expresses and mathematically covers the complete main question, with no additional hypothesis found. Fresh isolated Lean, kernel and external-checker results must be supplied by the coordinating audit before an overall “Verification passed” conclusion. No Lean or Lake command was executed by this reviewer.

| Required judgment | Current judgment | Decisive evidence or missing action |
| --- | --- | --- |
| Is the proof about the specified original question? | Yes, for the main question (1.1). | Original printed p.171 was read and visually inspected; the complete divisor list, real exponent, constant and cofinal positive witnesses match. |
| Has the exact commit actually passed the new verification? | Not completed in this sub-review. | The two independent layout jobs must finish, including all 18 target checks. Historical receipts are not substituted. |
| Does it completely solve the specified original question? | Mathematical coverage is complete; final verified verdict pending. | Every obligation of the main question is mapped below; execution and closure checks remain necessary. |
| Does it satisfy the Lean completeness requirements? | Not yet confirmed by this sub-review. | No static veto was found; the final decision requires the exact-commit execution evidence. |

## Fixed input and retrieved history

- Awards PR: [#691](https://github.com/TheJustinSunPrize/awards/pull/691); related claim [#1351](https://github.com/TheJustinSunPrize/awards/issues/1351).
- Awards base: `TheJustinSunPrize/awards`, branch `main`, `ff33abd13163e789790eb1014e55f57c05f94432`.
- Awards head: `ketianzhang1-lang/awards`, branch `jsp-000912-kz-full-formalization`, `2c1242af9bc691f0c052c46c309baa6b197458a2`.
- Proof: `ketianzhang1-lang/jsp-000301-lean`, branch `jsp-000912-complete-proof`, commit `bf99214b3104d89c628abb9c824a56d89a6bd6fe`, project `projects/jsp-000912`.
- Local checkout HEAD matched this proof commit and its worktree was clean before review. The coordinating run should retain its own remote branch-ancestry receipt.
- Complete current API lists contained one changed file, six PR commits, zero ordinary PR comments, zero reviews, zero inline review comments and zero claim comments; API totals and list lengths agree. `submission-snapshot.json` retains the responses and retrieval time. A final head reread is still required before publishing the aggregate report.

The sole current diff changes the Lean-proof field and adds Attribution basis; the problem description and status fields are unchanged. The corrected complete-proof submission appears in commit `75faf61c9e78f62373287c0721916a2bd50556b4`. The earlier incomplete-transfer history must not be used to backdate this complete source or the new self-check.

## Original source and scope

The primary source is P. Erdős, [“Some problems and results on additive and multiplicative number theory”](https://users.renyi.hu/~p_erdos/1981-33.pdf), 1981, printed p.171, equation (1.1) and its next paragraph. The PDF was found through the Rényi Institute's [author bibliography](https://users.renyi.hu/~p_erdos/Erdos.html), downloaded and its first page visually inspected. SHA-256: `55e7d25c6cf2467214bdcc1e0d8e55678ad8909571102c9b74d98afe82c13682`.

The source asks, for each real exponent greater than one, whether the sum of powered relative gaps between all consecutive positive divisors is below a fixed constant for infinitely many integers. Factorials and least common multiples are proposed witness candidates, not additional required conclusions. The unpowered logarithm-adjusted question (1.2) is introduced separately and identified as a consequence. Thus this audit covers (1.1); it does not certify factorial/lcm bounds or a separately formalized (1.2).

The Erdős-problem webpage and LaTeX endpoint returned HTTP 403. They are not treated as freshly read evidence; the primary paper supplies the actual statement. Vose's 1984 paper is credited bibliographically, as in the fixed catalog; this review did not obtain its full text or use it to certify the submitted construction.

## Coverage matrix and proof-path review

All locations below refer to the fixed [FullProof.lean](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/bf99214b3104d89c628abb9c824a56d89a6bd6fe/projects/jsp-000912/FullProof.lean). The matching five-module layout has exactly the same proof bodies.

| Requirement | Definition/declaration and fixed lines | Correspondence and boundary review |
| --- | --- | --- |
| Complete positive-divisor list | `sortedDivisors`, `hAlpha`, lines 672–677; membership, strict ordering and adjacency lemmas, 679–725 | Standard `Nat.divisors`, sorted increasingly, zipped with its tail. Every adjacent pair is included once; ratios and powers are real. Positive witnesses remove the `Nat.divisors 0` convention. |
| Actual consecutive divisors rather than a selected grid | `Consecutive`, 187–189; `grid_consecutive_gap`, 195–215 | The predicate forbids every intervening divisor. A grid witness inside a hypothetical large gap contradicts this predicate. |
| Every exponent strictly above one | `jsp_000912_full`, 773–788; `lower_gap_weight`, 474–502 | `exists_nat_ge` chooses a natural r with `4 ≤ r*(α−1)`. Nothing excludes exponents arbitrarily close to one; r changes with α. |
| A uniform finite bound | `hAlpha_candidate_bound`, 752–769 | Explicit bound `64*(16*r*(r+1)+2)^2` is independent of construction index K. No limiting, density or unproved grid assumption appears in the endpoint. |
| Arbitrarily large positive witnesses | `candidate_pos`, 329–330; `index_le_candidate`, 339–346; endpoint, 773–788 | `candidate r M` is positive and at least M for every natural cutoff, including M=0. Cofinality on naturals entails infinitely many witnesses. |
| Both halves and central crossing of the divisor list | `Consecutive.reflect`, 577–593; `reflected_below_anchor`, 603–614; `all_gap_cost`, 633–664 | Complementary-divisor reflection preserves the ratio. The binary anchor is itself a divisor, so a crossing pair cannot bypass it. No uncontrolled upper or central gap is omitted. |
| Finite summation and telescoping | `potential_sum_telescope`, 728–736; `potential_sum_le`, 738–749 | The potential lies in [-1,1] at every divisor; telescoping bounds the entire list, including empty-adjacency cases. |
| Literal strict bound in the original source | `Verify912.literal_formula`, `Verify912.intended` in each audit bridge | The new bridge defines the sum directly from Mathlib operations, proves equality to the submitted definition, then chooses C+1 to turn the submitted weak bound into a strict bound. |

All 800 standalone lines were read, including the finite-radix construction, dyadic size estimates, weighted decay and potential argument. The endpoint has only the original exponent condition; auxiliary assumptions are discharged by proved lemmas. There are no section/typeclass hypotheses that package the conclusion as an assumption. Static scanning found no project `axiom`, `sorry`, `admit`, native decision, kernel-skipping, custom elaborator, foreign implementation or environment mutation. This scan is supporting evidence only; it does not replace fresh transitive closure checks.

## Static source and contribution checks actually performed

`static-review-checks.json` records fresh checks of all 14 entries in `SOURCE_SHA256SUMS`, independent comparison of standalone/modular bodies, and application of `LEAN4_34_PORT.patch` to recovered commit `9074d0cebd4e132a6c1fa71c0817693246935398` with zero fuzz. All six proof files were reconstructed byte for byte. The inspected patch changes compatibility tactics/APIs and the environment header, with no mathematical statement or construction change.

The standalone file imports Mathlib only; the modular files import Mathlib and preceding local modules. The repository has an MIT license. The source uses a personal-name attribution with OpenAI assistance; the applicant account is `ketianzhang1-lang` and identity remains unverified. Repository/source attribution is not completed independent identity verification. Mathematical credit remains with Michael D. Vose (1984).

[Issue #24](https://github.com/TheJustinSunPrize/awards/issues/24) registers an already existing full formalization in `plby/lean-proofs`, pinned at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`; its source and author notices are acknowledged by this submission. The local implementation does not import that proof. The claim of independent development is an author statement; this review can verify source separation and history, not private chronology. No first-formalization, exclusive authorship or award-priority verdict is given. An attempted repository-wide issue search was unavailable through the connector, so the related-record review is not represented as exhaustive.

## Exact execution inputs for the coordinating audit

Two isolated runner keys are supplied, `912-full` and `912-modular`, for the same proof commit. Each has a `config-*.json`, `targets-*.json` and `bridge912-*.lean`. Each target list contains the original seven audited declarations plus `Verify912.literal_formula` and `Verify912.intended`: 9 targets per layout, 18 checks in total.

The standalone group imports `FullProof` and `FullProof.VerificationBridge`. The modular group maps each original target to its actual definition module and imports `JSP912.VerificationBridge`. **Do not import both layouts into one Lean process**, since they deliberately share declaration names. Export and run NaNoda separately for each group.

- Toolchain: `leanprover/lean4:v4.34.0`; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`; nine locked dependencies.
- Default build includes both `FullProof` and `JSP912`; no source bootstrap or external-source download is required.
- Original verifier: `bash scripts/verify.sh`; evidence directory `evidence/current`.
- It checks source synchronization/checksums, warning-as-error builds, six kernel replays, seven closure checks under each layout, actual dependency revisions and a rejected false-arithmetic negative control.
- Run the official per-target audit for both manifests, bridge kernel replay, and independent exports/NaNoda with only `propext`, `Classical.choice`, `Quot.sound` permitted. `scripts/verify_nanoda.sh` historically exports the standalone group only, so it does not replace the new modular independent check.

## Submission wording corrections

Use “complete main divisor-gap existence theorem (Erdős 1981, p.171, equation (1.1))”. Explain the strict-bound bridge and uniform constant, and identify both checked layouts. Keep historical Lean 4.19 logs and run 35265836287 separately labelled. Replace the old pending-self-check passages only with actual new run results, dates and fixed report links after both jobs finish.

Retain disclosure of the prior plby formalization, mathematical solver credit, source-history correction and pending contributor identity check. The JSON proof list should contain the single selected proof version, not evidence-only commits or cited dependencies. Do not backdate the new self-check to before opening the existing PR. Do not check a merged-PR declaration while PR #691 remains open; solver registration, organizer mathematical review, catalog eligibility and award allocation remain external prerequisites.

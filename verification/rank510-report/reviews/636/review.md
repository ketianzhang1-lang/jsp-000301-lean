# JSP-000636 / Erdős 776 — independent semantic review

**Provisional overall conclusion: evidence insufficient until the separately orchestrated isolated execution completes.** Static review of proof commit `5c23ecf6211449c9bd7f4ac9229300ed43f666b2` finds a complete match to the original threshold-estimate question, including exact multiplicity, arbitrary finite ground sets, eventual attainment and impossibility, genuine least-cutoff semantics, quantitative estimates and the claimed limiting ratio. No statement mismatch or missing mathematical premise was identified. This document does not claim a fresh successful Lean run.

| Required question | Current judgment | Decisive evidence or remaining check |
| --- | --- | --- |
| Is the object proved the specified original problem? | Yes, at the semantic-review level | The original request is for threshold estimates; the endpoint and the independently expanded bridge retain all its parameters and both existence and impossibility. |
| Has this exact commit actually passed the new audit? | Not completed by this review task | The parent verification run must supply clean-build, target, kernel and external-checker results for the 82 listed targets. |
| Does the submission completely solve the original problem? | Cannot yet certify; all original obligations are covered by the source statements | Execution and transitive trust checks remain necessary; no additional proof obligation was found by static review. |
| Does it meet the Lean completeness requirement? | Cannot yet certify | Upgrade only after successful execution and trust review; registration, identity, merge and award decisions are separate. |

## Fixed input and evidence

- Review date: 2026-09-19 UTC. Exact acquisition times are in `github-snapshot.json`, `primary-source.json` and `static-source-audit.json`.
- Awards PR: [#382](https://github.com/TheJustinSunPrize/awards/pull/382), claim [#1353](https://github.com/TheJustinSunPrize/awards/issues/1353).
- Awards base: `TheJustinSunPrize/awards`, `main`, `ff33abd13163e789790eb1014e55f57c05f94432`.
- Awards head: `ketianzhang1-lang/awards`, `jsp-000636-antichain-upper-kz`, `7b918856f1732ddde1d03a6398ac66d5d52144f5`.
- [Base entry](https://github.com/TheJustinSunPrize/awards/blob/ff33abd13163e789790eb1014e55f57c05f94432/problems/catalog-0601-0700.md#JSP-000636) and [head entry](https://github.com/TheJustinSunPrize/awards/blob/7b918856f1732ddde1d03a6398ac66d5d52144f5/problems/catalog-0601-0700.md#JSP-000636): the problem-description field is unchanged. The single-file diff updates mathematical status, Lean-proof information, attribution and publication evidence. Eligibility remains No.
- All PR files (1), commits (4), reviews (0), inline comments (0), ordinary PR comments (0), and claim comments (0) were retrieved. No pagination gap was found; all lists are shorter than the requested 100-item page.
- Lean repository: `https://github.com/ketianzhang1-lang/jsp-000301-lean`; branch `jsp-000636-pair-label-upper-kz`; project `projects/jsp-000636`; selected commit `5c23ecf6211449c9bd7f4ac9229300ed43f666b2`.
- Local Git HEAD equals the selected commit. The fetched named branch tip also equals it; `merge-base --is-ancestor` returned 0. Runtime checks should independently repeat this identification.
- Scope: exactly this complete proof version. Earlier proof revisions and historical runs are source-history/evidence references, not additional selected submissions.

## Original question, independently obtained

[He and Tang, arXiv:2602.09803v1](https://arxiv.org/html/2602.09803v1#S1), Problem 1.1, asks for estimates of the eventual cutoff for antichains of subsets of an n-element ground set, with exactly r distinct members at each occupied size. For each r greater than one, above the cutoff the family can contain r(n−3) members but cannot contain r(n−2). Remark 1.2 identifies the exact-r and at-least-r conventions for the maximum number of occupied sizes. Definition 1.3 uses the least cutoff with strict condition n greater than that cutoff. The r=1 sentence is background to the question for r>1. The paper also proves sharper error estimates than this Lean package claims.

The full public HTML was retrieved independently and hashed for internal source review. `primary-source.json` records its URL, timestamp and digest. The original print references cited by that paper were not separately obtained; no claim of inspecting those print editions is made. Use the stable arXiv link in public deliverables rather than republishing the downloaded paper.

## Semantic coverage matrix

All Lean links below identify the selected commit. Coverage here means statement and proof-chain coverage established by manual review; the corresponding `targets.json` entries remain pending until execution.

| Obligation | Lean declarations and definitions | Correspondence and scope | Audit target evidence |
| --- | --- | --- | --- |
| Distinct ordinary subsets and inclusion antichain | [JSP000636.lean](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5c23ecf6211449c9bd7f4ac9229300ed43f666b2/projects/jsp-000636/JSP000636.lean), lines 19–26 and `antichain_iff_isAntichain` | `Finset (Finset (Fin n))` prevents repeated members. `Antichain` explicitly says inclusion between members forces equality; the lemma proves agreement with Mathlib's ordinary `IsAntichain`. No new order instance is introduced. | Original targets t0–t13; bridges `Verify636.original`, `Verify636.intended`. |
| Exactly r members at each occurring cardinality | Same file, `ExactMultiplicity` and `card_eq_mul_size_count`; [Thinning.lean](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5c23ecf6211449c9bd7f4ac9229300ed43f666b2/projects/jsp-000636/Thinning.lean), `thin_to_exact` | The count uses a filter by ordinary `Finset.card`. Levelwise thinning retains the occupied sizes and antichain condition. `r>0` is discharged from r≥2. Cardinality r times level-count is proved, not stipulated. | t9, t10, t59–t61; expanded exact-r condition in both main bridges. |
| Every multiplicity r≥2, a uniform finite cutoff and every larger n | [Threshold.lean](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5c23ecf6211449c9bd7f4ac9229300ed43f666b2/projects/jsp-000636/Threshold.lean), `attaining_family`, `threshold_upper_bound`, `threshold_exists` | The cutoff is the explicit expression 2r+4⌊√r⌋+7; n>N becomes n≥2r+4⌊√r⌋+8. It depends only on r, not on n or a chosen family. Pair-label capacity is proved for every such parameter, so r=2 and r=3 are included. | t51–t58 and construction targets t38–t50. |
| Attainment and impossibility, on every finite ground set | [OriginalQuestion.lean](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5c23ecf6211449c9bd7f4ac9229300ed43f666b2/projects/jsp-000636/OriginalQuestion.lean), `mapFamily_*`, `finite_type_card_le`, `finite_type_attaining_family`, `original_threshold_question` | Ground-set equivalences preserve family cardinality, member cardinality, inclusion and each level count. The terminal theorem constructs the required exact-r family and excludes the larger cardinality. No prescribed labeling or chosen witness is assumed. | t71–t78 and `Verify636.original`. |
| A genuine maximum and the actual least eventual cutoff | [Lower.lean](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5c23ecf6211449c9bd7f4ac9229300ed43f666b2/projects/jsp-000636/Lower.lean), `extremal`, `IsThreshold`; [Asymptotics.lean](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5c23ecf6211449c9bd7f4ac9229300ed43f666b2/projects/jsp-000636/Asymptotics.lean), `exactExtremal`, `exactExtremal_eq`, `threshold_exact_spec` | `Finset.univ` ranges over all finite families, including the empty family. The finite supremum is therefore the maximum. `Nat.find` is used only after threshold existence is proved; the leastness theorem quantifies over every alternative cutoff N. The independent bridge defines the extremal profile using literal inclusion and level-count conditions. | t55–t65; `Verify636.profile_eq`, `Verify636.intended`. |
| Lower and upper estimates and sharp leading growth | `critical_size_bound`, `threshold_lower_bound`, `threshold_bounds`, `threshold_relative_bound`, `threshold_ratio_bound`, `threshold_ratio_tendsto` | For r≥4 the critical obstruction at n=2r+2 forces every valid cutoff to be at least 2r+2. The proved uniform upper estimate has square-root error. The real ratio tends to 2 through all natural r. Natural subtraction is used only with justified size bounds in the relevant extremal arguments. | t35–t37, t58, t65–t70; `Verify636.intended`. |

The eight source proof modules were read in full. The construction's `HalfFamily` structure has proof fields, but those fields are actually constructed in `assembleHalf` and `pairLabel_half_exists`; the endpoint does not assume the existence of an admissible structure. The critical lower-bound chain establishes the shared star center and then bounds both halves of the middle level, contradicting multiplicity. Thinning supplies the exact-r condition. None of these essential steps is replaced by a theorem parameter equivalent to the desired conclusion.

Boundary review: r=0,1 are outside the original threshold-estimate domain. The total `threshold` function assigns 0 there solely to express a sequence on all naturals; this does not affect the eventual real limit. Uniform upper estimates include r=2,3, but the package does not calculate their exact threshold values. The n≥4 hypothesis of the universal obstruction is correctly discharged by the eventual cutoff. No logarithmic error term or exact piecewise formula is claimed. These stronger results are not obligations of the original estimate question.

## Audit configuration and checks still required

`targets.json` contains all 79 declarations from the committed `Audit.lean` plus three named audit bridges, for 82 targets across eight source modules and one harness module. Every target belongs to at least one independently identified requirement. The bridge defines its own profile using ordinary finite subsets, inclusion and cardinality, then connects it to the submitted extremal function; it does not merely rename a suspicious source definition.

The bridge belongs at `JSP000636/VerificationBridge.lean` and imports `OriginalQuestion`. It must be added only to the isolated verification checkout, without editing the committed proof or Lake configuration. `config.json` records the project, commit, branch, module list, verifier command and evidence directory.

Lean is pinned to `leanprover/lean4:v4.34.0`. Mathlib is pinned to `5ed2965256430c3649e86755f9576b54eca72435`; all nine dependency revisions must be compared against actual checkouts. No bootstrap or non-Mathlib proof dependency is needed. The default library roots explicitly include all eight proof modules.

The committed `scripts/verify.sh` performs `lake build --wfail`, eight explicit `leanchecker` replays, all 79 axiom reports, all nine dependency-pin comparisons and a false-arithmetic negative control. The parent harness additionally must run the unchanged official audit script on every target and bridge and export their complete dependency closure for the independent checker. The script pins `lean4export` to `6cea97789dc088ea47fcea15692db85685aedac5` and NaNoda to `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.

Static scanning of the eight source modules found no custom axiom, sorry/admit, native evaluation, environment-editing elaborator, kernel-skipping option or external implementation attribute. This is only a locator check; the fresh transitive axiom reports and external checker are still necessary. Historical successful runs and historical axiom logs are not a substitute.

One metadata observation: the committed manifest's top-level `name` is `JSP000728`, whereas the Lake package is `JSP000636`. The dependency revisions and project files are otherwise pinned. Do not silently repair this field. Run the original package and report any actual consequence or automatic manifest change; a harmless descriptive mismatch alone is not a mathematical defect.

## Contribution and overlapping work

The selected repository's [PROVENANCE.md](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5c23ecf6211449c9bd7f4ac9229300ed43f666b2/projects/jsp-000636/PROVENANCE.md) identifies `ketianzhang1-lang`, with ChatGPT/Codex assistance, as the implementation contributor, and credits He and Tang for the mathematics and Erdős/Trotter for the problem and obstruction. Public source history is corroborating evidence, not identity verification or an award decision.

The seven prior proof modules match commit `36da76e793678ee6a062f1703674fd3789334cbd` byte for byte; the eight final ground-set/endpoint theorems are in `OriginalQuestion.lean`. `static-source-audit.json` contains all comparisons and the complete local import list. Imports contain only the eight local modules and Mathlib; no competing Lean proof is imported. `LICENSE.LEAN` retains the supplied Apache license text.

[PR #677](https://github.com/TheJustinSunPrize/awards/pull/677) and [claim #679](https://github.com/TheJustinSunPrize/awards/issues/679) were freshly read. They concern a different development claiming a stronger exact threshold formula, retaining credit to mthiim and contributors for a substantial reused core. This review does not certify that separate proof. Its earlier publication relative to this submission's asymptotic supplement and its overlapping scope must remain disclosed. Do not claim first formalization, an exact formula, improved mathematics or exclusive credit.

## Required submission wording updates

1. Replace the old uncompleted-self-check banner and section with the actual new run's date, exact checked proof SHA, report, target totals, standard-axiom result and specific independent-checker scope, but only after those results exist. Keep historical run `35296708689` separately labeled historical.
2. Keep a single selected proof object. Remove the current live PR's boilerplate about additional JSON objects identifying dependencies; this PR contains only one selected proof version.
3. State the claim as complete formalization of the original threshold-estimate question. Explicitly retain the square-root error, all r≥2 upper cutoff, r≥4 lower bound, actual leastness and limit. Keep the exclusion of stronger exact or logarithmic refinements.
4. Add the current solver-registration prerequisite and mathematical-review status. Selecting both submission-type boxes reflects submission of He–Tang solver information plus this applicant's Lean contribution; it does not mean the applicant claims the solver role. The award claim remains Lean-only.
5. Preserve the historical pre-opening self-check checkbox as unchecked unless organizer guidance resolves it. A September 19 audit cannot be backdated to the September 17 PR opening.
6. Add the current original-source/self-contribution declaration and new claim declarations. The official PR is still open; the claim's merged-PR declaration must remain unchecked. Do not equate successful proof verification with solver registration, accepted authorship, eligibility, merge or award approval.
7. Provide immutable report/harness links and copyable complete English PR/claim bodies. The selected proof commit is unchanged; a later evidence commit is a different object and must be labeled accordingly.

Public snapshot references should omit unrelated contact details and the downloaded full paper. The report, target manifest, bridge, source hashes and relevant source/attribution URLs are sufficient public review materials.

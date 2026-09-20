# JSP-000728 / Erdős 877: semantic and attribution review

**Static conclusion: the fixed endpoint corresponds to the original relative-count question, including its fixed exponential-saving form. No statement mismatch or extra unproved hypothesis was found in the reviewed source. Fresh execution is pending the parent audit; this document alone is not a Verification passed verdict.**

| Required judgment | Current answer | Evidence |
| --- | --- | --- |
| Is the proof about the specified original question? | Yes, for the original Cameron–Erdős relative-count question identified below. | Independent source, actual finite-family definitions, and the two relative-count conclusions agree. |
| Did the selected commit actually pass fresh verification? | Not yet established by this static review. | The parent audit must supply the actual build, 35 target results, replay and external-checker logs. Historical run 35300095687 is not a substitute. |
| Does it completely solve that original question? | Full semantic coverage found; a final Yes awaits execution and trust checks. | Both little-o and fixed positive exponential saving are present without an assumed counting bound; the all-N lower bound is also proved. |
| Does it satisfy this audit's Lean completeness requirement? | Not yet established by this static review. | Requires the pending checks on precisely the selected commit, including all bootstrap dependencies. |

## Fixed inputs and current GitHub state

Reviewed on 2026-09-19 UTC. Original API responses and capture time are in `github-snapshot.json`, `related-snapshot.json` and `proof-metadata.json`.

- Awards PR: [#373](https://github.com/TheJustinSunPrize/awards/pull/373), open, head `f6336c16b2f6d06ca2a7e829a36cb4056389338d`, `ketianzhang1-lang/awards:jsp-000728-lower-bound-evidence`.
- Base: `TheJustinSunPrize/awards:main`, `ff33abd13163e789790eb1014e55f57c05f94432`.
- Claim: [#1480](https://github.com/TheJustinSunPrize/awards/issues/1480).
- Selected proof: [ketianzhang1-lang/jsp-000301-lean](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/22212651d30af02ad36f01a206984d31b0ec75c6/projects/jsp-000728), commit `22212651d30af02ad36f01a206984d31b0ec75c6`, branch `jsp-000728-lower-bound-kz`, project `projects/jsp-000728`. The branch API resolved to this exact commit during this review; the selected commit API exists.
- One changed file, `problems/catalog-0701-0800.md`, matches `changed_files=1`. All five commits were retrieved and match `commits=5`. PR ordinary comments, inline comments, reviews, and claim comments each returned an empty complete first page. No review comments were omitted from this observation.
- The diff changes only `Lean proof` and adds `Attribution basis`. It does not rewrite the original problem description, mathematical status or `Eligible to claim` field. The base description is broad, so the submission must continue to identify its precise original relative-count scope instead of claiming every later sharp refinement.
- The current online PR omits the new completed self-check section and includes the upstream dependency in the proof-submission JSON. Replace the JSON with the sole selected proof version and list upstream material separately as an attributed dependency.

## Independent problem source and scope

The independently accessed primary paper [Balogh, Liu, Sharifzadeh and Treglown, arXiv:1409.5661v1, Section 1](https://arxiv.org/html/1409.5661v1#S1), dated 19 September 2014, explicitly records the earlier Cameron–Erdős question: whether maximal sum-free sets are negligible relative to all sum-free sets, and whether a fixed positive exponential saving holds. It separately records the all-N lower construction, distinguishes inclusion maximality, and permits repeated summands. The later sharp exponent and residue-class constants are stronger refinements, outside this package's claim. The 2001 Łuczak–Schoen article is identified in that paper's references and in the unchanged catalog publication record. The Erdős problem page and direct AMS PDF were inaccessible through the web tool; the successfully accessed paper gives the requisite precise statement, so no mathematical scope was inferred solely from the submitter's README.

Let M(N) count all inclusion-maximal sum-free subsets of {1,…,N}; let F(N) count all sum-free subsets. Sum-free means that no x,y,z in the set satisfy x+y=z, including x=y. The submitted endpoint establishes both original relative-count alternatives and additionally establishes the classical lower bound for every natural N.

The broad catalog wording does not itself prescribe a particular sharp asymptotic. This review concerns the original question expressly identified in the PR. Maintainers must approve that statement correspondence and the contribution scope; the report cannot decide award eligibility or silently expand the proved statement to later sharp estimates.

## Coverage matrix

All local source references below are relative to the fixed project root. The rows describe semantic coverage; actual check results must be attached separately.

| Obligation | Precise meaning and boundaries | Definition / theorem evidence | Semantic finding |
| --- | --- | --- | --- |
| Sum-free sets | No x+y=z with all three members; x=y is allowed. | `JSP000728.lean:18`, `SumFree`; `JSP000728Bridge.lean:17`, `sumFree_iff_upstream`. | The local predicate forbids sum membership for every pair, with no distinctness assumption. The independent bridge uses a literal three-variable equation formulation. |
| Whole ambient interval | The set is contained in all of `Finset.Icc 1 N`. | `JSP000728.lean:21`, `MaximalSumFree`. | Positive integers 1 through N, inclusive. Natural-number representation does not admit zero as a member. |
| Inclusion maximality | No strictly larger sum-free subset of that same interval contains A. | `MaximalSumFree`; `JSP000728Bridge.lean:25`, `maximalSumFree_iff_upstream`. | The quantifier ranges over every finite candidate B; equality orientation is reversed explicitly when translating upstream. This is not maximum cardinality. |
| Actual maximal count | Enumerate every maximal set, not only constructed examples. | `JSP000728.lean:25`, `maximalSets`; `JSP000728Bridge.lean:37,42`, `maximalSets_eq_upstream`, `maximalSets_card_eq_upstream`. | Full powerset filter with exact equality to the imported family and count. |
| Actual all-set count | Enumerate every sum-free subset of the interval. | `JSP000728Bridge.lean:48,52`, `allSumFreeSets`, `allSumFreeSets_eq_upstream`. | Full powerset filter. The upper-half construction is only a subset used to establish a lower bound. |
| All-N maximal lower bound | `2^(N/4) <= M(N)` with natural division, for every N including zero. | `JSP000728.lean:35–145`, culminating in `cameron_erdos_lower_bound`; `JSP000728Complete.lean:30`, `upstream_count_lower_bound`. | Odd-pair seed, maximal extension and an injective binary-choice map. The `N/4=0` branch extends the empty set, so small and zero intervals are handled. |
| Benchmark for all sets | `2^ceil(N/2) <= F(N)` and `2^(N/2) <= F(N)` in real exponent notation. | `JSP000728Bridge.lean:60,76,84`, `upperHalf_powerset_subset`, `allSumFreeSets_lower_bound`, `benchmark_le_allSumFreeSets`. | The upper half has `N-N/2` elements. Every subset is sum-free because two members sum above N. The denominator count is positive for every N. |
| Imported maximal upper bound | M(N) is little-o of `2^(N/2)`, and eventually `M(N)<=2^(c*N)` for one c<1/2. | `JSP000728Complete.lean:19,24`; upstream `Erdos877.erdos_877`, `erdos_877_exponential_bound`, `resolutionExponent_lt_half`. | No counting theorem is a parameter of the endpoints. `Resolution` partitions the whole maximal family; its temporary enumeration assumption is discharged by `Enumeration.eventually_sumFreeCount_le_pow`. |
| Original negligibility question | `M(N)=o(F(N))`; ratio tends to zero as N tends to infinity. | `JSP000728Complete.lean:36,48`, `maximalCount_isLittleO_allCount`, `maximal_to_all_ratio_tendsto_zero`. | Uses the actual-count benchmark comparison. The limit is a theorem in addition to the endpoint's little-o conjunct. |
| Stronger original exponential form | There exists one real delta>0, independent of N, with the bound eventually. | `JSP000728Complete.lean:54`, `relative_exponential_saving`. | Witness is `1/2-resolutionExponent`; positivity is proved, and real-power multiplication gives the benchmark. There is no N-dependent delta or fixed finite-N sample. |
| Complete conjunction | Lower bound, relative little-o and exponential saving all hold together. | `JSP000728Complete.lean:76`, `jsp_000728`; independent `Verify728.intended`. | Every original alternative is covered, together with the separately claimed lower bound and ratio limit. |

## Independent audit bridge and target routing

`bridge728.lean` introduces its own three-variable `Verify728.SumFree`, inclusion-maximality predicate, and full powerset counts `M` and `F`. It proves the predicate equivalences and count equalities before deriving a statement containing the lower bound, little-o, ratio limit and fixed exponential saving. Thus its intended statement is not a renaming of the submitter's definition.

The official `targets.json` contains **35 targets**: all 27 original `AuditComplete.lean` names and eight bridge declarations. Five bridges perform the independent semantic comparison; three explicitly typed import bridges additionally expose the original upstream benchmark results. Every bridge and original target needs `#check`, `#print` and `#print axioms`.

Three original targets are defined in bootstrap-fetched `ErdosProblems/Erdos877.lean`, not in a Git blob in the submitting repository. Their manifest `module=AuditComplete` and `source=AuditComplete.lean` designate the actual tracked verification entry that imports and audits those names, while `definition_source` records their real definition path. This does not claim that AuditComplete defines them. The 43 upstream sources must still be hash-checked, rebuilt and replayed. `upstream-target-routing.json` records the correspondence.

## Source, dependencies and execution requirements

- Exact toolchain: `leanprover/lean4:v4.34.0`; retain the original `lake-manifest.json` and verify all nine actual dependency revisions. No `lake update`.
- `UPSTREAM.json` pins 43 sources: 14 Erdős-877 modules, 23 Erdős-565 modules and six Erdős-76 modules, from `plby/lean-proofs` commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
- All 43 original Git blob SHA-1 values, original SHA-256 values and final compatibility-port SHA-256 values were verified independently in `reviews/728/upstream`, without executing Lean or changing the fixed proof checkout. They comprise 753,135 bytes / 18,082 lines after the prescribed port. Hashes are in `upstream-sha256.json`.
- Eight dependency files have explicit compatibility edits. They rename removed if/dif lemmas, add a Ring tactic import, adjust one tactic sequence and add attribution notices. No theorem statement, assumption or axiom is weakened by the recorded changes. Most sources retain a historical 4.33 header; this package is the recorded 4.34 compatibility port, not a claim of unchanged 4.33 execution.
- Prepare with `python3 scripts/bootstrap.py`, `lake exe cache get Mathlib`, `lake build Mathlib`. The bootstrap only retrieves fixed bytes and performs the listed transformations; static review found no credentials or unrelated writes.
- Run original `bash scripts/verify.sh` without `--resume`; it invokes `verify_complete.py`, compiles all 47 modules (43 upstream plus three local proof files plus the audit) sequentially, checks 27 original axiom closures, checks nine dependency SHAs, runs four kernel-prefix replays and requires a false-arithmetic negative control to fail.
- Original verifier output directory is `evidence-complete`, distinct from the committed historical `verification` directory. Preserve historical logs and avoid reporting them as the fresh run.
- The default Lake library roots include `JSP000728`, `JSP000728Complete` and `AuditComplete`, so the complete endpoint is not omitted by the default build. The new audit bridge is an explicit additional target.
- `config.json` gives the project, branch, commit, bootstrap/cache and verification details for the parent isolated runner. This reviewer did not execute Lean, Lake, proof scripts, kernel replay or NaNoda locally.

The static scan across the three local proof modules and all 43 fetched sources found no occurrences of `sorry`, `admit`, custom `axiom`, `native_decide`, `trustCompiler`, `debug.skipKernelTC`, `implemented_by`, `extern`, custom elaborators, or unsafe definitions. Existing `#print axioms` commands are expected. This scan is only a locator: actual transitive axiom checks, clean builds and the independent checker remain necessary before a passed verdict.

## Attribution, related records and source history

The original lower-bound module in this proof is byte-identical to both proof revision `91fdee92a0e9122b9e41cfd3b24d0ab70a64b3c0` and the original catalog-submission file at awards revision `fa77d5ecf712a1e0fadfdd642eeaf50ac1162968`. These two immutable files were freshly retrieved and compared with the selected local source; `source-history-check.json` records the identical hashes. The separate documentation at `39874257f3b9df912caf3619c89fd4d72fafaf03` is supporting source-history evidence, not another selected proof version.

The concrete submitter contribution is the all-interval implementation of the classical lower construction, exact family/count bridges, upper-half injection, integration and relative-count consequences, compatibility port and reproduction workflow. The final conjunction uses the lower construction directly; the relative upper bound itself instead uses the imported upper proof plus the all-set benchmark. An earlier lower-bound-only submission must not be presented as an earlier complete solution.

The upstream upper proof predates the submitter's lower-bound contribution according to the disclosed source history. Its entry credits Codex and GPT-5.6 Sol, and its source/license notices remain retained. [PR #1326](https://github.com/TheJustinSunPrize/awards/pull/1326), freshly read, records the same pinned upstream formalization and expressly disclaims proof authorship or award entitlement for the catalog recorder. This related submission must remain disclosed. Issue #24 was also read but does not contain a JSP-000728 record; do not cite that unrelated batch issue as specific evidence for this problem.

Mathematical credit and formalization credit must remain separated. No first formalization, ownership of the imported upper proof, new informal mathematics, exclusive entitlement or independent human certification is established by this review. Broader priority/identity/award allocation remain for the organizers.

## Replacement-text recommendations and external prerequisites

1. Use a precise title, for example: `JSP-000728: complete relative-count proof with our all-interval construction and attributed upper development`.
2. Keep only `22212651d30af02ad36f01a206984d31b0ec75c6` in the selected-proof JSON. Cite upstream `8822f7d...` as a pinned attributed dependency and the historical source-evidence revision separately.
3. Replace the obsolete “fresh self-check not completed” material only after the parent audit actually completes. The new section must identify official skill commit, verification date, exact proof commit, all four required judgments, complete report and public run/evidence links. Distinguish 27 original targets, 35 fresh official manifest targets, 47 original rebuilt modules and the separately checked bridge module.
4. Preserve the original-question scope and the explicit exclusion of later sharp exponent/residue-class conclusions. Do not write “complete sharp enumeration” or imply authorship of the complete imported argument.
5. Retain pending solver registration and mathematical review. Keep the organizer-unapproved statement status. Do not mark a retrospective self-check as performed before this old PR was opened.
6. In claim #1480, disclose that PR #373 is still open/unmerged and keep any “merged proof PR” declaration unchecked. Preserve the account-to-contributor evidence and pending identity verification. The existing historical “no award claim found on 2026-09-18” sentence is unnecessary and can be removed to avoid confusion with the present claim.
7. Keep public text English. No external PR/claim mutation or comment was performed by this reviewer.

The deliverable package should contain this review, targets, bridge, configuration, metadata/hash evidence and the parent run's actual logs. Publishing or organizer acceptance is a separate event from preparing a copyable replacement.

## Audit routing correction after the 2026-09-20 attempt

Run 35477208711 completed the unchanged original clean verifier and all eight independent/import bridge targets. Its official audit exited 2 solely because eight original declarations in `JSP000728Bridge.lean` were routed to `lake build +JSP000728Bridge`, while the original Lake roots include only `JSP000728`, `JSP000728Complete` and `AuditComplete`. The definition file is compiled and replayed by the original verifier, but is not a standalone Lake module target.

The corrected manifest routes these eight declaration checks through the tracked, configured `JSP000728Complete.lean` verification entry, which imports their actual definition module. Each target records `definition_source=JSP000728Bridge.lean` and its exact hash. No original source, original Lake configuration, bridge code or official audit script is changed. The original clean compilation and kernel replay of the actual definition module must still be retained in the next run. `entry-routing.json` lists the affected declarations. The failed attempt is a routing failure, not a completed overall verification verdict.

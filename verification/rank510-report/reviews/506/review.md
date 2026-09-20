# JSP-000506: semantic review of the two fixed submissions

**Current conclusion: evidence insufficient for a fresh verification verdict until the isolated execution finishes.** Static review identifies complete original-problem coverage in both versions, with explicitly scoped supplemental claims in the second. No semantic mismatch or missing assumption was found in the reviewed endpoints. This document does not claim that either selected commit has passed the new run.

| Required judgment | Main complete package | Selection supplement |
|---|---|---|
| Does the statement express the original problem? | Yes: full-sequence divergence in probability of the random-graph chromatic–cochromatic gap | Yes: unchanged complete endpoint, plus separately scoped consequences |
| Has the exact commit actually passed this fresh audit? | Not yet established here; use its own execution results | Not yet established here; use its own execution results |
| Is complete resolution established by this fresh audit? | Awaiting actual checks and dependency closure | Awaiting actual checks and dependency closure |
| Are Lean completeness requirements satisfied? | Not yet determined | Not yet determined |

Review date: 2026-09-19 UTC. Public replacement text should remain English. The official skill and all five references were read at awards revision `38e63c424c7196f8d4ceb664c5c25f0c0529d5e2`.

## Fixed inputs

| Field | Value |
|---|---|
| Awards PR / claim | [PR #363](https://github.com/TheJustinSunPrize/awards/pull/363), [claim #1623](https://github.com/TheJustinSunPrize/awards/issues/1623) |
| Awards head | `ketianzhang1-lang/awards`, `27fddf6dee0d9fb92a34643f05615da57be80574` |
| Awards base | `TheJustinSunPrize/awards`, `ff33abd13163e789790eb1014e55f57c05f94432` |
| Main proof | `ketianzhang1-lang/jsp-000301-lean`, branch `jsp-000506-complete-kz`, commit `2aca2f16eba715d7ad672dfa017481b647c00063` |
| Selection proof | Same repository, branch `jsp-000506-selection-20260919`, commit `90e1298ec99973eefe607f9c21bfffa750804087` |
| Project | `projects/jsp-000506` in each separate checkout |
| Toolchain | `leanprover/lean4:v4.31.0`; Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`; nine manifest pins |
| Upstream mathematical/Lean proof | Samuil Petkov, `SamPetkov/Erdos` at `b3fdc4d3efbe6c999faac3da4614cc3036b3b3ea` |

Both local checkout HEADs match their designated commits and their tracked worktrees were clean. Complete API collections contain one changed file, four commits, no reviews, no inline comments, no PR comments, and no claim comments. The base/head catalog comparison changes only the Lean proof field and adds attribution; the problem description, mathematical status, eligibility and original bibliographic references are unchanged. Branch ancestry and final remote-head stability must be recorded by the execution harness.

The original `JSP000506.lean`, both integration modules, Lake configuration, toolchain, lockfile, upstream manifest and original audit targets are byte-identical in the main and selection versions; hashes are in `static-evidence.json`. Equality of those files does not let a check of one commit certify the other.

## Independent original source and mathematical scope

[Heckel, arXiv:2408.13839v1, Section 1](https://arxiv.org/html/2408.13839v1#S1) explicitly restates the Erdős–Gimbel question: whether a deterministic divergent gap threshold is exceeded with probability tending to one for `G(n,1/2)`. Her Proposition 3 is a finite concentration reduction with a high-probability small-gap premise. Her later Conjecture 4 asks for matching order `n/log(n)^3`; that stronger two-sided conjecture is separate from the original yes/no divergence question. The distinction matters: a lower bound of a positive divergent scale resolves the original question without proving a matching upper bound. The source itself distinguishes its earlier partial progress from a full positive answer.

Direct access to erdosproblems.com/625 returned HTTP 403. The independently inspected Heckel primary paper and the unchanged base catalog provide the original-question evidence; the inaccessible page is not represented as read.

The pinned [Petkov manuscript](https://github.com/SamPetkov/Erdos/blob/b3fdc4d3efbe6c999faac3da4614cc3036b3b3ea/625/arxiv/main.tex) was independently retrieved. Its main theorem includes a uniform lower bound with coefficient
`C = (log 2)^2/4 * log(200/153) > 0`. The manuscript's formal-verification section expressly limits the Lean theorem to that uniform bound; its phase-dependent refinement is a manuscript-only claim. The final proof paragraph says a matching upper bound and optimal constant remain open. Therefore neither a matching upper bound, an exact asymptotic equality, nor the phase-dependent refinement should be added to this submission's verified scope. Attempts to access the arXiv Petkov record were unavailable; the fixed author-repository manuscript is the source actually read.

## Coverage matrix

All entries below describe semantic coverage; actual compilation, replay and axiom checks remain separate obligations.

| Original or expressly claimed obligation | Declaration / definition | Reviewed correspondence and boundaries |
|---|---|---|
| All simple undirected labelled graphs on n vertices | `Edge`, `toGraph`, `fromGraph`, `graphEquiv`; round-trip theorems | Ordered representatives u<v give each unordered edge exactly once. No loops, multiplicities or graph-family restriction. The bijection includes n=0 and n=1. |
| Independent fair edge choices | `mass`, `mass_event_eq_randomGraph`; upstream `randomGraphMeasure` | Rational cardinality divided by 2 to the number of possible edges is exactly the Mathlib binomial graph law at probability 1/2, not a numerical approximation. All events in the finite measurable graph space are measurable. |
| Ordinary chromatic number | `Proper`, `chi`, `proper_iff_colorable`, `chi_eq_chromaticNumberNat` | `Nat.find` has an explicit n-colour witness; comparison with Mathlib's finite chromatic number is proved. |
| Minimum partition into cliques or independent sets | `CoProper`, `zeta`, `coProper_iff_all_pairs`, `coProper_iff_coColorable`, `zeta_eq_cochromaticNumber` | Every colour class has its own clique/independent flag. Pair conditions cover all distinct vertices. Empty colour classes do not change a minimum. The n-colour witness handles empty and nonempty orders without an empty-infimum default. |
| Real gap agrees with natural subtraction | `zeta_le_chi`, `gap_cast_eq` | Every proper colouring is a cocolouring, so natural subtraction is untruncated on the actual inputs. |
| Positive, explicit quantitative lower scale | `Erdos625.gapConstant_pos`, `quantitative_gap_tendsto_one` | Exact C*n/(log n)^3 with natural logarithms; all graph orders in the limit. No finite sample evidence or subsequence replaces the limiting assertion. |
| Scale actually diverges | `gapScale_tendsto_atTop` | Proved via exponential domination of logarithmic powers and positive C. Small n where log terms vanish do not affect eventual limits. |
| Original full-sequence question | `fixed_threshold_tendsto_one`, `jsp_000506` | Every fixed real threshold and every natural threshold. The literal ≥ convention is harmless: for strict fixed M, use M+1; for the original divergent strict threshold, use half the quantitative scale once that scale is positive. This is convergence in probability, not an almost-sure pathwise claim under an unspecified coupling. |
| Variable thresholds | `threshold_tendsto_one` | Arbitrary deterministic real functions eventually bounded by the quantitative scale; no monotonicity assumption. |
| Equivalent small-gap consequence | `small_gap_probability_tendsto_zero`, `eventually_not_heckel_premise` | Integer successor threshold identifies the complement exactly; the old 999/1000 premise eventually fails at every fixed width. |
| Retained finite concentration reduction | `concentration_reduction`, `heckel_proposition3`, `complete_package` | The finite statement retains its explicit premise and all orders/widths. That premise is not an assumption of the unconditional complete endpoint. |
| Independent semantic challenge | `Verify506.coColourable_iff`, `coNumber_eq`, `intended`, `explicit_quantitative`, `explicit_scale_diverges` | Auditor-defined vertex-pair cocolouring predicate and least number, standard binomial graph law, literal real gap and numerical coefficient. These bridges still import the submitted environment and are not an isolated comparator specification. |

The natural-number original endpoint is not itself a two-sided estimate for gap size. References to “chromatic lower / cochromatic upper” in the upstream dependency describe the two invariants used to obtain a lower bound for their difference, not upper and lower bounds for the gap.

## Selection supplement: all eleven added theorem claims

| Added targets | Exact scope and assumptions |
|---|---|
| `intersection_probability_lower` | Finite inclusion–exclusion lower bound P(A∩B)≥P(A)+P(B)−1 on the uniform cube; no independence. |
| `conditional_failure_bounds` | Positive retained mass is explicit. Conditional failure is at most unconditional failure divided by retained mass. No assertion about conditioning on mass zero. |
| `joint_gap_probability_bounds` | Gap events for one graph and its actual complement. The complement preserves uniform mass but is not independent. The lower bound is the union bound, not multiplication of probabilities. |
| `joint_quantitative_gap_tendsto_one` | The same quantitative scale holds simultaneously for the graph and complement. |
| `joint_threshold_tendsto_one` | Two separately chosen threshold functions, each eventually below the proven scale. |
| `conditional_joint_failure_bounds` | Factor two is from the complement union bound; positive conditioning mass remains explicit. |
| `conditional_joint_gap_tendsto_one` | Requires eventual positive retained mass and failure-probability / retained-mass ratio tending to zero. It does not assert arbitrary rare-event conditioning preserves the conclusion. |
| `positive_mass_conditioning_tendsto_one` | A fixed positive lower bound on retained mass and an eventually admissible threshold suffice. The retained sets may depend arbitrarily on the graph. |
| `mean_minimum_pair_gap_lower` | Exact finite uniform expectation of min(gap(G),gap(complement G)); lower-bounded by threshold times joint success probability. Negative thresholds also cause no problem because the gap is nonnegative. |
| `mean_minimum_pair_gap_scale_lower` | For every fixed c<1, eventually E[min gap]≥c*scale. No matching upper bound or asymptotic equality is claimed. |
| `mean_minimum_pair_gap_tendsto_atTop` | Divergence follows from the preceding lower bound at c=1/2 and divergent scale. |

The additional auditor bridges explicitly unfold the conditional intersection/quotient and the finite-sum expectation. The original complete theorem does not acquire these supplemental conditioning hypotheses.

## Upstream proof trace and trust boundary

The fetched standalone proof has 3,896,926 bytes, 89,528 lines and 480 distinct embedded module boundaries. Its SHA-256 is
`53060b9563330f20a5f2133ffdf8f56e5a41eae6d0f772487193d9c54133e837`;
the Git blob SHA is `3df42367a79afc10af5b024b19fe1a6026b3c945`. Both were independently checked against the immutable bootstrap manifest. No compatibility edits or renames are applied.

The endpoint `Erdos625.erdos625` at source line 88448 instantiates the conditional assembly theorem using proved cocolouring seed, chromatic lower-tail probability limit, rounding budget and root separation. The reviewed key declarations are:
`erdos625Statement_of_uniform_seed_and_root` (15316),
`randomGraphMeasure_chromaticNumberAtMost_phaseChromaticLowerIndex_tendsto_zero` (38661),
`fixedOffset_rounding_budget_spec` (84822),
`exists_eventually_concrete_phase_fixedOffset_root_gap` (85143), and
`exists_phaseCochromaticFixedOffset_real_seed` (88345).
Their intermediate hypotheses are discharged at the final endpoint; the final statement has no seed, moment, concentration or root-gap parameter.

The 89,528-line source has not received a line-by-line independent human proof review here. The inspection traced the original objects, endpoint and substantive premise-discharge chain; fresh transitive axiom inspection, kernel replay and an independently implemented checker must provide the mechanical dependency evidence. The static keyword scan found only explanatory occurrences, and is not a substitute for those checks.

## Runtime instructions and audit entries

`config.json` has the two exact versions and commands. Prepare pinned inputs online, then execute the original verifier offline in the isolated environment. Neither local Lean nor Lake was run during this review.

Main: `bash scripts/verify.sh` delegates to `verify_complete.py`, which fresh-compiles five source units with warnings as errors, checks all nine dependency revisions, audits 49 original targets, replays four prefixes and checks the false-arithmetic negative control. Do not pass `--resume` for the clean reproduction.

Selection: `python3 scripts/verify_selection.py` verifies preservation against the base Git object, runs that complete verifier, explicitly compiles the selection module, audits 60 original targets, replays its extra prefix and applies an additional negative control. The base commit object must exist in its clone. `JSP000506Selection` and its audit are omitted from the default Lake target.

The independent exporter must use commit `8554815c2dc6b7abe99ec1f08849c9759ba77947` with the 4.31 toolchain; NaNoda is pinned to `4c544ed4099c8227f07d5de77ad1e69fb0740a27`. The allowed axioms are precisely `propext`, `Classical.choice`, `Quot.sound`, with unpermitted axioms treated as hard errors. Original NaNoda shell scripts fetch tools online, so prepare the same pins before the offline execution instead of trying to run their network preparation inside it.

All 49 / 60 original audited declarations are retained. The full reviewer manifests add six / eight bridge declarations, totaling 55 / 68 respectively. Four upstream declaration targets use the tracked, configured `JSP000506Complete.lean` as their verification entry; the real definition file is separately recorded as `definition_source: Erdos625SelfContained.lean`. This is necessary because the original complete source is checksum-fetched and absent from the submitter commit's Git tree. The original verifier fresh-compiles and kernel-replays that actual definition source; the mapped entry must not be described as the definition file. No official audit script or proof source is changed.

## Attribution and replacement-text corrections

The applicant's 19-theorem finite formalization of Heckel's reduction is distinct from 26 local integration/consequence theorems and the selection supplement's 11 additions. The complete quantitative mathematical and Lean result is credited to Samuil Petkov. His unchanged imported proof, CC BY 4.0 license/scope/citation files and AI-assistance notices remain preserved. Apache 2.0 for the applicant's own additions does not relicense the imported work. No new mathematics, first-formalization priority, exclusive authorship or independent human verification should be asserted.

[PR #1073](https://github.com/TheJustinSunPrize/awards/pull/1073) and [claim #1075](https://github.com/TheJustinSunPrize/awards/issues/1075) were withdrawn by their author, who explicitly identified the mismatch between deterministic Erdős 762 and random-graph Erdős 625. [PR #1599](https://github.com/TheJustinSunPrize/awards/pull/1599) is also now **closed**; its author closed it on 2026-09-19 because it registered another contributor's proof. The existing claim calls this PR “open”; replace that stale word. Its reference to the same deterministic proof does not supply random-graph overlap evidence. [PR #40](https://github.com/TheJustinSunPrize/awards/pull/40) is a catalog evidence registration whose author disclaims authorship and prize share. Complete issue bodies and the relevant comments are saved separately.

Recommended correction to the affected paragraph:

> The closed PR #1599 by zjukop3 references the same external deterministic formalization and revision. Its author closed it on 19 September 2026 because it registered another contributor's proof. We disclose it for attribution and statement-scope review; it does not establish a solution of the random-graph problem.

After fresh execution, add separate exact-version results for main and selection. Historical 49/60-target receipts must remain labelled historical and cannot certify the new 55/68-target audit. Retain the distinction between source, proof, harness and report commits. Avoid claiming the source README's historical “undergoing full verification” line is a current report; link the dated fresh report.

The current official catalog still has eligibility “No”. Identity review, solver registration, maintainer acceptance and merged status are separate from Lean completeness. These older PRs cannot truthfully check a declaration that this new supplemental self-check occurred before their original opening. Leave any untrue merged/timing declaration unchecked and explain the chronology.

## Stored evidence

`github-snapshot.json` contains complete current PR/claim and collection responses.
`related-source-snapshot.json` and `related-comments.json` retain base/head catalogs and attribution evidence.
`Petkov-manuscript.tex` is the immutable primary mathematical manuscript actually inspected.
`Erdos625SelfContained.lean` is the verified upstream static snapshot.
`static-evidence.json` records byte identity, source hashes, nine pins and scan limitations.
`506-main-targets.json`, `506-selection-targets.json`, the two bridge files and `config.json` are the frozen audit inputs.

This review must be completed with the fresh isolated logs before a final verification verdict is issued.


## Fresh execution, first candidate: auditor-bridge failure

The first fresh isolated run, workflow `35476644569`, finished both original complete verification procedures successfully. Its official target audit also passed all **49** original main declarations and all **60** original selection declarations. Both augmented audit jobs nevertheless failed because the auditor's `explicit_scale_diverges` bridge used `simpa only [Erdos625.gapScale, Erdos625.gapConstant]` on a theorem with the unapplied function `Erdos625.gapScale` as the argument of `Tendsto`. The simplifier did not unfold that unapplied definition, producing a type mismatch at line 67 of each bridge. Consequently none of that bridge module's six/eight target checks completed; no overall success is inferred from the original declarations' success.

The replacement proof of this unchanged bridge statement is:

```lean
  change Tendsto Erdos625.gapScale atTop atTop
  exact JSP000506.gapScale_tendsto_atTop
```

The named scale is definitionally equal to the displayed explicit constant times `n / log(n)^3`; the `change` command requires Lean to check that equality. This changes only the auditor's bridge proof. The selected submission revisions, mathematical statement, target sets and official audit implementation remain unchanged. The selection adapter successfully compiled all eleven original selection targets and needs no modification. A fresh isolated rerun, including its new strict bridge precheck and every original and official audit stage, remains necessary before calling the 55/68-target checks complete.

Raw first-run failures are retained under `evidence/506-main-failed-1/remote` and `evidence/506-selection-failed-1/remote`; the failed candidate is not presented as final proof of compliance.


## Final isolated rerun and downloaded-evidence inspection

The corrected audit harness `1e52e4f5851d9751ddc637d383e365047b749fad` completed both jobs successfully in workflow [35479940510](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35479940510) on 20 September 2026. The selected proof commits were unchanged.

| Version | Job | Official target audit | NaNoda declarations | Artifact files verified |
|---|---:|---:|---:|---:|
| Main | 105995827916 | 55/55 | 60,143 | 362 |
| Selection | 105995827933 | 68/68 | 60,196 | 448 |

Each downloaded ZIP matched GitHub's artifact SHA256, and every internal evidence file matched its recorded checksum. The independent read-only inspector validated original fresh verification, exact source and dependency identities, the official script's unchanged hash, every declaration's actual transitive axiom output, strict bridge compilation, bridge kernel replay, the independent exporter/checker and original false-arithmetic negative controls. All observed axioms were within the three permitted standard axioms; some declarations use fewer or none.

Selection additionally recorded exactly nineteen successful manual-equivalent builds: eleven of the original selection module and eight of the auditor bridge. All used the pinned Lean executable with warning-as-error/resource flags, unchanged exact source hashes, separate compile logs and recorded output artifact hashes. The adapter's limited scope remains disclosed above. These mechanical passes supplement the separate semantic review; they do not certify official eligibility, solver registration or maintainer acceptance.

Main ZIP SHA256: `6441be01d629a5a6947fca69b8df5b20c6b42c9e37fe3de60029ae77808add44`.
Selection ZIP SHA256: `de5639768f7c87db4b67df8495810a117cfbf53582e6a2d496ccac1630d9cc45`.

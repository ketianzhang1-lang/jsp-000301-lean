# Updated lean-verify self-check: JSP-000391 and JSP-000438

**Overall conclusion: verification passed for both submissions in the specified scope.** At the three exact proof commits listed below, the submissions fully formalize Stoll’s arbitrary-base construction (JSP-000391) and the all-order tree Ramsey bound with the claimed sharpness and multicolor extension (JSP-000438). Statement correspondence, full obligation coverage, unchanged-source builds, all 37 target checks, kernel replay and independent exported-proof checking succeeded. This report concerns formal proof completeness, not mathematical priority, candidate registration, award eligibility, or payment.

Prepared on 2026-09-19 UTC. Public-facing text is in English at the contributor's request. The audit follows the official [lean-verify skill at commit 38e63c424c7196f8d4ceb664c5c25f0c0529d5e2](https://github.com/TheJustinSunPrize/awards/tree/38e63c424c7196f8d4ceb664c5c25f0c0529d5e2/skills/lean-verify). This is a contributor-commissioned self-check, not certification by an independent human referee.

## Required judgments

| Question | JSP-000391 | JSP-000438 |
|---|---|---|
| Does the formal statement express the specified problem? | Correspondence established for Stoll's arbitrary-base construction; scope explained below | Correspondence established for the all-order two-color upper bound and uniform sharpness |
| Has the specified commit actually passed all required checks? | Yes: 14/14 targets and both replay levels succeeded | Yes: 13/13 and 10/10 targets and both replay levels succeeded |
| Does it completely solve the specified problem? | Yes, for the explicitly stated arbitrary-base construction | Yes, for the all-order upper bound and claimed extensions |
| Does it meet this audit's Lean completeness requirements? | Meets the Lean completeness requirements within the stated trust boundary | Meets the Lean completeness requirements within the stated trust boundary |

## Fixed inputs

| Item | JSP-000391 | JSP-000438 |
|---|---|---|
| Awards PR | [293](https://github.com/TheJustinSunPrize/awards/pull/293) | [408](https://github.com/TheJustinSunPrize/awards/pull/408) |
| Awards base repository / branch | TheJustinSunPrize/awards / main | TheJustinSunPrize/awards / main |
| Awards base SHA | `ff33abd13163e789790eb1014e55f57c05f94432` | `ff33abd13163e789790eb1014e55f57c05f94432` |
| Awards head repository | ketianzhang1-lang/awards | ketianzhang1-lang/awards |
| Awards head branch | `jsp-000391-digit-evidence` | `jsp-000438-tree-ramsey-kz` |
| Awards head SHA | `2ef7ea9c4456874876fb5b72629241a730c7ab41` | `4a27bd6c9f1982f33982fceb49c33e1ffe62f8a7` |
| Original problem | Erdős 482; Stoll's general-base digit construction | Erdős 547; tree Ramsey upper bound |

The base and head catalog descriptions were compared; neither PR narrows the problem text. The proof repository is [ketianzhang1-lang/jsp-000301-lean](https://github.com/ketianzhang1-lang/jsp-000301-lean). These are proof commits, distinct from the awards PR commits:

| Manifest | Proof commit | Project | Submitted branch |
|---|---|---|---|
| `391-targets.json` | `14e5155e68554de4e053e4aacd77095a93e96dd4` | `projects/jsp-000391` | `jsp-000391-digit-recurrence` |
| `438-main-targets.json` | `5f94d026ec88696bb5047506c433ad401e5f02ef` | `projects/jsp-000438` | `jsp-000438-sharp-stars-kz` |
| `438-color-targets.json` | `0175b2a7a50f7687ece92f61bbe0e3a2f377913a` | `projects/jsp-000438` | `jsp-000438-multicolor` |

All three commit objects were fetched and checked out exactly. The selected commits are ancestors of their stated branch tips; `evidence/source-trace.json` records the local check and remote artifacts record it independently. The final API recheck at 2026-09-19T15:42:34+00:00 confirmed both awards PR heads and the official rules commit were unchanged. The PR commit collections contain five and seven entries respectively. Review, ordinary-comment, and inline-comment reads returned empty collections. No replacement with a newer proof version was made.

## Statement review and coverage

### JSP-000391

Primary source: [Stoll, On Families of Nonlinear Recurrences Related to Digits](https://cs.uwaterloo.ca/journals/JIS/VOL8/Stoll/stoll56.pdf), Theorem 1.3 on printed page 3 and its proof in section 2.2. The claim audited is existence of the stated alternating floor recurrence for every integer radix and positive target; it is not a classification of all floor recurrences or a claim that the original square-root-of-two coefficients work unchanged in every base.

For a natural radix `g ≥ 2` and real `w > 0`, normalize `t = w / g^⌊log_g(w)⌋`. The audited source uses an actual recursive sequence starting at 1, coefficients `a = g / ((g−1)(t+g))` and `b = (g−1)(t+g)`, and every shift `−1/g ≤ e < (g+1)(g−2)/g`. The source's zero-based sequence index is one less than the paper's. The independently written audit recurrence and digit function are linked to the submitted definitions in `bridge391.lean`.

| Obligation | Submitted definitions / proof and audit bridge | Semantic finding |
|---|---|---|
| Every radix and positive target | `normalized`, `stoll_general_base`, `Verify391.intended` | No bounded radix, rationality, computability or algebraicity premise; stronger real-target scope includes positive algebraic targets |
| Genuine recurrence and coefficients | `sequence`, `a`, `b`, `multipliers`, `Verify391.recurrence_eq` | Recursive definition, correct alternating parity, initial value 1, and `b = g/a` under the published hypotheses |
| Every digit, including leading digit | `digit`, `stoll_general_base`, `Verify391.digit_eq` | Floor differences, leading digit `⌊t⌋`, and the terminating rather than repeating-maximal-digit convention |
| Radix digit bounds | Targets in `391-targets.json` | Lower bound 0 and strict upper bound `g` |
| Reconstruction | `accumulated_eq_prefix` and the error/convergence targets | Exact decoded prefix identity, geometric error, and convergence to `t`; normalization supplies the radix exponent of `w` |
| Full shift interval | `admissible_shift` and `stoll_general_base` | Universal interval as published; `e = −1/g` is an admissible witness, including `g = 2` |

The proof uses paired induction, floor inequalities and finite geometric identities. The recursive sequence is not replaced by its intended closed form as an assumption. No additional local hypothesis asserting the desired digit identity was found.

### JSP-000438

The original problem is represented by the independently pinned [Formal Conjectures Erdős 547 statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/547.lean): for every tree of order `n ≥ 2`, the two-color diagonal graph Ramsey number is at most `2n−2`. Direct access to erdosproblems.com was unavailable (HTTP 403); that source limitation is retained. The reference corpus's placeholder proof is not imported by this submission.

| Obligation | Submitted proof and audit bridge | Semantic finding |
|---|---|---|
| Every order, every tree | `trees_monochromatic`, `tree_monochromatic`, `Erdos547.erdos_547`, `Verify438.direct` | All `n ≥ 2`, including 2; genuine finite simple trees and non-induced injective containment |
| Actual two-color Ramsey property | `RamseyDefinitions`, `Verify438.intended` | Explicit graph/complement alternative; a witness at `2n−2` prevents the natural infimum from exploiting an empty set |
| Proven extremal ingredient | `Erdos548.tree_free_edge_bound` in `Upstream548.lean` | Proven in the imported file, not passed as an assumption to the Ramsey theorem; the final weaker `erdos548` declaration is not being substituted for this ingredient |
| Optimal uniform bound | `sharpGraph_avoids_star`, `star_ramsey_even_order`, `tree_ramsey_bound_is_sharp`, `Verify438.sharp` | Explicit cyclic graph on `4k+1` vertices and its complement avoid the star on `2k+2` vertices; equality `4k+2` for every `k`, including 0 |
| Full two-color theorem in the second claimed version | Targets in `438-color-targets.json` | Rechecked separately at its exact commit; no mixing of compiled evidence across commits |
| Multicolor extension | `multicolor_tree_embedding`, `Verify438Color.intended` | Arbitrary finite nonempty color type, prescribed trees of orders at least 2, host size `2 + ∑c (m c−2)`, actual injective monochromatic embedding under every edge coloring |

Sharpness means no uniformly smaller bound for all tree orders: the even-order stars attain it. It does not claim that every individual tree attains `2n−2`, nor that this equality holds for stars of every parity. The multicolor statement is an additional claimed result and is therefore included in the audit scope.

The imported extremal proof was traced to [tadamcz/erdos548 at 82ffb751f3d37768927df9239ed08439bbe0dd09](https://github.com/tadamcz/erdos548/blob/82ffb751f3d37768927df9239ed08439bbe0dd09/Erdos548/Resolutions/Erdos548_192usd_21h.lean). The submitted port retains the credited upstream work. Its central chain is rooted-word counting → tree-free edge bound → color-graph edge counting → monochromatic containment. The port notes document library/API adjustments. Both audited 438 versions have the same port SHA-256, `460409e526f8a52c96fa0163073c9b6d9cbeb36722823a800cb172457e4b6602`; the original reference file SHA-256 is `7e5f0d9a5573eef054dee6831edf7e785ea689f03f53cb800b896b12d3277fa1`.

## Execution protocol and trust boundaries

The proof sources are unchanged. Audit bridges are added only to disposable checkouts after an original clean project build. Each version receives its own manifest, output directory and full target checks (14, 13 and 10 declarations, respectively).

1. Fetch the exact proof and official skill commits; record source commit, branch tip and ancestry.
2. Build a disposable Docker image using the submitted Lean 4.34.0 toolchain. Download the nine manifest-pinned dependencies and the trusted Mathlib cache while online.
3. Prepare lean4export at `6cea97789dc088ea47fcea15692db85685aedac5` and NaNoda at `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.
4. Disable container networking. Run as UID 10001 with no credentials, all capabilities dropped, no-new-privileges, two CPUs, 6 GiB memory and a 512-process limit. Only disposable proof/evidence directories are writable; the harness is read-only.
5. Remove project build outputs; execute `lake build --wfail` and the submitted verifier. Preserve fresh evidence separately and restore only any committed historical evidence logs to their original contents.
6. Run official `audit.py preflight` and `audit.py run`. For every target, explicitly build the module, recheck the source and record `#check`, full `#print`, and transitive `#print axioms`.
7. Replay the audit bridge with `leanchecker`. Export all target dependency closures and run NaNoda with only `propext`, `Classical.choice`, and `Quot.sound` permitted.
8. Verify all actual dependency Git revisions and tracked input hashes; archive exact commands, exits, durations, logs and target results.

Mathlib is fixed at `5ed2965256430c3649e86755f9576b54eca72435`. Its dependency cache is retained; this is a clean rebuild of the submitted project, not a source rebuild of the entire Lean compiler and all Mathlib. The independent checker adds a separate implementation but does not remove trust in its own implementation, runtime, hardware, or source acquisition. The bridges restate the intended definitions independently but import the submitted proof environment; they are not a separately compiled clean-room comparator. Natural-language correspondence remains an explicit semantic review.

Static source scans found no proof placeholders, custom axioms, native-decision shortcuts, or kernel-check bypasses in the submitted Lean source. Fresh target execution independently confirmed that every one of the 37 targets depends on exactly `propext`, `Classical.choice`, and `Quot.sound`; no native-computation axiom or unproved mathematical axiom occurs in these closures. `axiom-results.md` lists the complete result for every target, with full declaration output in the raw audit logs. Ordinary classical Lean axioms are not proof gaps.

## Run history and results

The [fresh run 35452081149](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35452081149) completed successfully for all three versions using harness commit `c288f7ba520d8a84520c84395609f1b32e94df49`. All commands listed below exited 0.

| Version | Targets | Original clean build | Official target audit | Bridge kernel replay | Independent NaNoda result |
|---|---:|---:|---:|---:|---|
| 391 | 14 | 35.93 s | 204.64 s | 9.48 s | Checked 17408 declarations with no errors |
| 438-main | 13 | 18.22 s | 122.13 s | 8.73 s | Checked 11279 declarations with no errors |
| 438-color | 10 | 37.25 s | 69.45 s | 3.73 s | Checked 10993 declarations with no errors |

The original module kernel replays also succeeded in the submitted verifier; the false-arithmetic controls were rejected with the expected `1 = 0` diagnostic. The local source hashes match before and after execution, and all nine actual dependency revisions match the pinned manifest. Only the added audit bridge remains untracked. Artifact ZIP hashes and every archived internal file hash were verified after download.

`evidence/execution-summary.json` records exact durations, command arguments, working directories, image identifiers, manifest hashes, branch tips and dependencies. `/out/...` paths in the raw logs map to the corresponding `evidence/<version>/remote/...` directory in this bundle. The executed manifests retain `coverage: pending`, because the automatic script does not make semantic judgments; `reviewed-manifests/` contains separately labeled post-review copies with full coverage, without altering the original execution evidence.

The helper reports `checker_compatibility: not_probed` because it does not probe external tools itself. That prerequisite was separately discharged by the successful Lean 4.34.0 kernel and pinned NaNoda runs recorded here. The preflight manual prerequisites were reviewed against the workflow, Docker image metadata, original build logs, dependency revisions, source hashes and inspected module mappings.

The initial [run 35451765722](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35451765722) failed during Rust installer download. The second [run 35451881698](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35451881698) failed while writing image metadata after ownership had already transferred to the container UID. Neither failure tested the mathematical proof. The harness was repaired without changing any selected proof commit.

## Submission consequences

This self-check occurs after the existing awards PRs were opened. It cannot truthfully establish that the new workflow ran before the original PR submission, and a pre-submission checkbox must not be backdated. The updated PR text should state the actual date, proof SHAs, report and run links and ask maintainers to apply the new policy to the existing submission.

The official process separately requires mathematical review and solver registration before Lean verification/candidate registration. This successful self-check does not register a candidate or make the open claim payable. Attribution must distinguish Stoll's mathematical result (391) and the credited upstream extremal proof (438) from the contributor's Lean development, port, integration and extensions.

The official awards repository previously rejected attempted updates with HTTP 403. This audit does not assert that the official PRs or claims have been updated. Prepared replacement text and evidence should remain reviewable until that write restriction is resolved.

## Reproducible artifacts

The audit branch `lean-verify-top2-20260919` in the proof repository contains `.github/workflows/lean-verify-top2.yml` and `verification/top2/`. The runner and configuration give the exact command order and working directories. Per-version manifests provide every fully qualified target name; evidence archives contain the official skill snapshot and SHA-256 manifest. GitHub Actions artifacts have 90-day retention, so durable copies of final evidence should accompany this report.


The included `target-index.md` provides commit-fixed file/line links for every declaration. The Chinese `how-to-lean-verify.md` explains the updated submission workflow. Raw artifacts and their official IDs, expiry dates and digest values are in `evidence/artifacts-metadata.json`; the bundled copies preserve them independently of GitHub retention.

Repository edition: raw execution archives are linked from [the successful workflow run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35452081149). The downloadable evidence bundle additionally includes those full archives and extracted logs; the lightweight report commit alone does not contain the compressed proof export.

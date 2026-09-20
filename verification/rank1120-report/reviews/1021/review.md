# JSP-001021: original-source and exact-version review

**Static semantic conclusion:** The selected proof completely disproves the historical universal formula posed by Erdős and Moser, with an explicit contradiction at n=15. It does not compute the extremal function at every order. The broader catalog wording and a competing lower-bound interpretation require organizer scope adjudication. New mechanical verification remains pending in this static review.

Reviewed at 2026-09-20T02:42:54.090379+00:00. This is a pre-execution semantic memo; it must be read together with the final actual CI/lean-verify evidence, not treated as a passed machine-verification report.

## Fixed objects

- Awards rules/base: `38e63c424c7196f8d4ceb664c5c25f0c0529d5e2`; submitted PR#699 head `80525e5901e034f4a8bad52e7ee1e8e6f532a0a8`; existing claim#1586.
- Selected proof: `7642a7f5eb190da6319b6ae7f11c829d7737e2dd`, branch `jsp-001021-tournament-verification`, project `projects/jsp-001021`.
- [Proof source](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/7642a7f5eb190da6319b6ae7f11c829d7737e2dd/projects/jsp-001021/JSP001021.lean), [source attribution](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/7642a7f5eb190da6319b6ae7f11c829d7737e2dd/projects/jsp-001021/PROVENANCE.md), [upstream pins](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/7642a7f5eb190da6319b6ae7f11c829d7737e2dd/projects/jsp-001021/UPSTREAM.json).
- All current catalog links and later verification/documentation commits were audited. `later-version-comparison.json` confirms they change only workflow, verifier integration, receipts/checksums or documentation, with no changed Lean proof, upstream manifest, module list or dependency pins. The selected proof remains distinct from those later commits.

## Independent original target

The [official catalog entry](https://github.com/TheJustinSunPrize/awards/blob/38e63c424c7196f8d4ceb664c5c25f0c0529d5e2/problems/catalog-1001-1022.md#JSP-001021) describes the guaranteed largest transitive subtournament in general language. Its cited [Erdős–Moser1964 original paper](https://real.mtak.hu/189065/1/cut_MATKUTINT_1964_1_-_2_pp125_-_132.pdf#page=3) was retrieved on 2026-09-20. The introduction, printed page 125, defines f(n) as the largest universally guaranteed transitive order. Section 1, printed page s126–127, states the logarithmic bounds and then explicitly raises the universal equality f(n)=floor(log₂ n)+1, including the n=15 case. The selected theorem refutes this universal equality; it does not assert a formula for all n. A single counterexample order suffices for that negative answer.

The original paper is primary evidence, not a search snippet. It distinguishes f(n) from the other function m(n) studied in later sections about representing oriented graphs by orderings. Those other sections are not the tournament-conjecture obligation. The Erdős Problems 1216 webpage itself returned 403. Related issue 1147 interprets the broad catalog summary as asking only for the known lower bound and disputes disproof submissions. The original source supports the universal-equality target, but the submission must disclose the catalog ambiguity rather than silently rewrite it. Any organizer-designated alternate target must be separately assessed.

## Coverage matrix

| Requirement | Formal declaration or definition | Assessment |
| --- | --- | --- |
| Tournament object | `Erdos1216.Tournament`, `Tournament.arc`; `Verify1021.encode15_arc` | Boolean complete orientations, no loops, opposite arcs complementary. Independent encoding shows every actual15-vertex relation satisfying these conditions is represented. |
| Transitive k-subset | `HasTransitiveTournament`; `fifteen_all_relations` | Injective map Fin k→Fin n with every earlier vertex pointing to every later vertex; no repeated-vertex loophole. |
| Actual f(n) | `Guaranteed`, `f`; `Verify1021.literal_extremal` | Greatest k≤n such that every tournament contains a transitive k-set. The independent definition exposes the quantified subset condition. |
| Fourteen-vertex dependency | `Erdos1216.directed_ramsey_five_fourteen`; `f_fourteen_eq_five` | Credited complete Reid–Parker proof and finite certificates; the exact14 result is an imported result. |
| All n≥14 and special n15 | `JSP001021.all_orders`, `fifteen_vertices`, `five_le_f_fifteen` | Restriction uses any chosen14 vertices and preserves orientation; no hypothesis on a special tournament. |
| Universal conjecture false | `JSP001021.jsp_001021`; `Verify1021.intended` | f(15)≥5 whereas floor(log₂15)+1=4; universal equality for all positive n is false. No exactf(15) or all-n formula is claimed. |
| Independent-reconstruction supplement | Three `JSP001021.LocalChecks` declarations | These certify only local exclusions,42 retained patterns and the final model's five-set. They are not misrepresented as a full Lean proof of the separate reconstruction. |

## Proof chain and checks

`JSP001021.jsp_001021` → `five_le_f_fifteen` → `guaranteed_fifteen`/`fifteen_vertices` → `all_orders` → upstream `directed_ramsey_five_fourteen`. The user-written `restrict14_arc` verifies the packed restriction preserves both orientations, including the reverse-order branch. The directed Ramsey proof descends to the fetched certificate module, using ordinary finite proofs rather than Python assumptions. The independent bridge defines another encoding from an arbitrary Boolean relation at 15, proves every arc is preserved, and transports the five-vertex ordered injection. This makes the relation-to-bit-vector correspondence explicit rather than merely repeating the original theorem name.

The submitted supplementary table checks 196 pairs,126 of which satisfy its intersection-size-one hypothesis;84 have explicit five-vertex witnesses and 42 are retained. Those certificates are additional targets but are not dependencies replacing the missing global reduction of the independent 15-vertex reconstruction. The full main route remains the credited 14-vertex theorem followed by transport.

## Provenance, licensing and overlap

Mathematical credit remains with K.B.Reid and E.T.Parker for the 1970 disproof. The imported14-vertex formal proof and certificate module at plby/lean-proofs8822f7ddef30fadbd92e1c6ab4ed897af356af5e retain Codex/GPT-5.6Sol attribution and explicit Apache 2.0 notices. The only documented port replaces deprecated `if_false`/`if_true` names with `ite_false`/`ite_true`; original and ported SHA256 values were independently recomputed. The applicant's MIT additions do not relicense the imports. Preserve the upstream source headers and `src/latest/LICENSE` notice (`inputs/UPSTREAM-LICENSE.txt`).

Applicant additions under ketianzhang1-lang with OpenAI assistance are the explicit restriction/orientation proof, all-orders transport, n15 endpoint, extremal disproof integration, local certificates and verification package. The original reproduction-only PR date is not a publication date for the later complete Lean proof. Overlapping disproofs include PRs 710,733,1196,1246 and their claims1198,1247; PR 1350 registers the existing upstream proof. Lower-bound/partial records include119,263,308/758,972/1147/1042. Credits, first priority and allocation remain for the organizers; no exclusivity or imported authorship is asserted.

## Exact execution plan and trust boundary

Lean 4.34.0 and Mathlib 5ed2965256430c3649e86755f9576b54eca72435; all 9 packages are fixed by the committed manifest. Bootstrap retrieves immutable upstream bytes, checks original SHA256 values, applies the disclosed mechanical port and checks port hashes. No proof-source mutation is needed. `bash scripts/verify.sh` performs clean source compilation with warnings as errors, full-module kernel replay, exact type checks, target transitive-axiom audits and a2+2=5 negative control. `check_built.py` alone is not a clean build.

Fresh verification is to run in a nonroot disposable GitHubActions container, offline during checking. No local Lean/Lake execution was performed for this review. All4original proof modules and all11public `Audit.lean` targets remain included. The added6bridge declarations give17total per-group target entries. The unchanged official auditor, strict bridge precheck, source/dependency stability hashes, full target export and NaNoda replay must succeed before a passed conclusion. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted; actual used subsets must be reported. Exporter4.34 compatibility rebuild is disclosed in the shared run record.

## Target inventory

| ID | Kind | Declaration | Verification entry | Definition source when different |
| --- | --- | --- | --- | --- |
| t000 | theorem | `Erdos1216.directed_ramsey_five_fourteen` | `JSP001021.lean` | `ErdosProblems/Erdos1216.lean` (SHA256 `352f0cc4def0150e62858792f60ca80b70088f97b53d020722b8e56f4a079491`) |
| t001 | theorem | `Erdos1216.f_fourteen_eq_five` | `JSP001021.lean` | `ErdosProblems/Erdos1216.lean` (SHA256 `352f0cc4def0150e62858792f60ca80b70088f97b53d020722b8e56f4a079491`) |
| t002 | theorem | `Erdos1216.not_erdos_1216` | `JSP001021.lean` | `ErdosProblems/Erdos1216.lean` (SHA256 `352f0cc4def0150e62858792f60ca80b70088f97b53d020722b8e56f4a079491`) |
| t003 | theorem | `JSP001021.restrict14_arc` | `JSP001021.lean` | Same file |
| t004 | theorem | `JSP001021.all_orders` | `JSP001021.lean` | Same file |
| t005 | theorem | `JSP001021.fifteen_vertices` | `JSP001021.lean` | Same file |
| t006 | theorem | `JSP001021.five_le_f_fifteen` | `JSP001021.lean` | Same file |
| t007 | theorem | `JSP001021.jsp_001021` | `JSP001021.lean` | Same file |
| t008 | theorem | `JSP001021.LocalChecks.local_exclusions` | `FiniteChecks.lean` | Same file |
| t009 | theorem | `JSP001021.LocalChecks.retained_count` | `FiniteChecks.lean` | Same file |
| t010 | theorem | `JSP001021.LocalChecks.final_transitive_five` | `FiniteChecks.lean` | Same file |
| t011 | bridge | `Verify1021.encode15_get` | `JSP001021/VerificationBridge.lean` | Same file |
| t012 | bridge | `Verify1021.encode15_arc` | `JSP001021/VerificationBridge.lean` | Same file |
| t013 | bridge | `Verify1021.fifteen_all_relations` | `JSP001021/VerificationBridge.lean` | Same file |
| t014 | bridge | `Verify1021.literal_extremal` | `JSP001021/VerificationBridge.lean` | Same file |
| t015 | bridge | `Verify1021.counterexample_at_fifteen` | `JSP001021/VerificationBridge.lean` | Same file |
| t016 | bridge | `Verify1021.intended` | `JSP001021/VerificationBridge.lean` | Same file |

Bootstrap-retrieved upstream definitions are not tracked project files in the selected commit. The official auditor therefore uses the unchanged tracked project entry that imports each exact declaration; the manifest separately preserves the actual definition path and its pinned port hash. The unchanged original verifier still compiles and kernel-replays every upstream module. This entry routing changes neither the checked theorem nor the selected proof source.

## Administrative conditions

This semantic assessment is not organizer approval, accepted solver registration, identity verification, merge or an award decision. The current catalog's Lean/eligibility statuses remain organizer-controlled. Existing PRs predate the revised pre-opening skill-check requirement: later checks cannot establish the historical pre-opening condition. Keep that declaration and the merged-PR claim declaration unchecked. Update the existing claim rather than silently asserting an exception or creating a duplicate.

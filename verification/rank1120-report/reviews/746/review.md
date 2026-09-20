# JSP-000746: original-source and exact-version review

**Static semantic conclusion:** The selected proof covers the complete catalog integer-graph assertion. The supplemental sharpness theorem concerns the number of labelled vertices, and does not assert minimum edge count. New mechanical verification remains pending in this static review.

Reviewed at 2026-09-20T02:42:54.090379+00:00. This is a pre-execution semantic memo; it must be read together with the final actual CI/lean-verify evidence, not treated as a passed machine-verification report.

## Fixed objects

- Awards rules/base: `38e63c424c7196f8d4ceb664c5c25f0c0529d5e2`; submitted PR#402 head `459668c825230b77e01bcb269ccb977090ddd4ab`; existing claim#1468.
- Selected proof: `4dfb40abe0cd1e538bbfccb1cc50f4829fb7383a`, branch `jsp-000746-sharp-kz`, project `projects/jsp-000746-sharp`.
- [Proof source](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/4dfb40abe0cd1e538bbfccb1cc50f4829fb7383a/projects/jsp-000746-sharp/JSP000746.lean), [source attribution](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/4dfb40abe0cd1e538bbfccb1cc50f4829fb7383a/projects/jsp-000746-sharp/PROVENANCE.md), [upstream pins](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/4dfb40abe0cd1e538bbfccb1cc50f4829fb7383a/projects/jsp-000746-sharp/UPSTREAM.json).
- All current catalog links and later verification/documentation commits were audited. `later-version-comparison.json` confirms they change only workflow, verifier integration, receipts/checksums or documentation, with no changed Lean proof, upstream manifest, module list or dependency pins. The selected proof remains distinct from those later commits.

## Independent original target

The independently pinned [official catalog entry](https://github.com/TheJustinSunPrize/awards/blob/38e63c424c7196f8d4ceb664c5c25f0c0529d5e2/problems/catalog-0701-0800.md#JSP-000746) asks about arbitrary triangle-free graphs on the integers. The full requested configuration has three distinct pairwise nonadjacent integers, one the sum of the other two. This is not a finiteness restriction on the integer graph. The catalog explicitly excludes the stronger open Hindman-set question.

The original Erdős Problems page 895 and forum were requested on 2026-09-20 but returned 403; that page is not represented as successfully read. A separately authored [Formal Conjectures statement at 0f34955e1a6841d31c59d76c99252423894752d1](https://github.com/google-deepmind/formal-conjectures/blob/0f34955e1a6841d31c59d76c99252423894752d1/FormalConjectures/ErdosProblems/895.lean) supplies the source reference Er95d, *On some problems in combinatorial set theory*,1995, pp 61–65, and distinguishes the solved finite integer-triple question from the open Hindman variant. Its formal statements contain placeholders and are comparison material only: they are neither imported nor treated as proved organizer-approved challenges. The 1995 original scan was not successfully obtained. The complete unambiguous catalog question, the independent finite formulation, and the submitted finite-to-integer map give the statement correspondence; this access limitation does not license any claim about solving the open variant.

## Coverage matrix

| Requirement | Formal declaration or definition | Assessment |
| --- | --- | --- |
| Arbitrary simple graph on ℤ | `JSP000746.jsp_000746`; `integer_graph`; `Verify746.intended` | The quantifier is over all integer graphs, not just bounded/finite graphs. The proof restricts internally to labels 1–18. |
| Triangle-free premise | `SimpleGraph.CliqueFree 3`; independent explicit triangle relation | `intended` converts the absence of three mutual edges to the standard clique-free premise. |
| Three distinct vertices and c=a+b | `jsp_000746`; `Verify746.intended` | All three distinctness conditions are explicit; `0<a<b` in the stronger witness implies that neither summand nor sum collapses. |
| Pairwise independent triple | Three separate negated adjacency clauses | No weakened single-nonedge or merely differently-labelled output. |
| Finite supplement for every n | `JSP000746Sharp.exact_threshold`; `Verify746.exact_finite_threshold` | Both directions for all natural n, including0; true exactly at n≥18. Fin n coordinatei means positive integeri+1. |
| Lower witness | `witness_triangle_free`, `witness_no_independent_schur_triple`, restrictions |43-edge17-vertex counterexample, restricted to every n≤17. Edge optimality is not asserted. |

## Proof chain and checks

`JSP000746.jsp_000746` → `integer_graph` → `Erdos895.finite_eighteen` → `core_contradiction_fin` → the kernel-generated LRAT proof. The injective map is i↦i+1 into ℤ; the sum coordinate is a.val+b.val+1, so the labels add correctly. Triangle-freeness pulls back through `SimpleGraph.comap`. The lower-threshold chain instead uses the explicit 17-vertex graph and ordinary `decide` proofs, then restricts it and combines with the upper bound.

A separate Python arithmetic inspection of the literal submitted edge list, recorded in `static-audit.json`, found43 distinct ordered canonical edges, zero triangles, and coverage of all 64 valid distinct-summand Schur triples on labels 1–17. This is supplementary source scrutiny, not a Lean/kernel check. The new bridge also checks the edge-list length with ordinary kernel reduction.

## Provenance, licensing and overlap

Ben Barber retains credit for the mathematical eighteen-vertex upper result. The fetched upper proof and CNF/LRAT certificates are attributed to Codex/GPT-5.6 Sol in plby/lean-proofs at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. The applicant's identified additions are the 43-edge witness, its finite checks and restrictions, sharp-threshold integration, actual-integer transport and reproduction package, with OpenAI ChatGPT assistance. No global first proof/formalization or minimum-edge result is asserted. Relevant earlier/overlapping records include issues18,19,1010,1157 and PRs165,738,1156,1164,1386. In particular PR 1156's forty-edge proposal is distinct from this vertex-threshold assertion.

The source retains original attribution headers. The upstream `src/latest/LICENSE` notice, copied to `inputs/UPSTREAM-LICENSE.txt`, states that externally sourced files carrying such notices are under Apache 2.0. No root-level upstream LICENSE exists at the pin. Do not apply the applicant's MIT license to upstream bytes, or infer a more specific license for an unmarked file from ownership. Preserve that notice and the exact original headers alongside any evidence snapshot; the submission itself points to upstream sources, not a new relicensing claim.

## Exact execution plan and trust boundary

Lean 4.34.0 and Mathlib 5ed2965256430c3649e86755f9576b54eca72435; all 9 packages are fixed by the committed manifest. Bootstrap retrieves immutable upstream bytes, checks original SHA256 values, applies the disclosed mechanical port and checks port hashes. No proof-source mutation is needed. `bash scripts/verify.sh` performs clean source compilation with warnings as errors, full-module kernel replay, exact type checks, target transitive-axiom audits and a2+2=5 negative control. `check_built.py` alone is not a clean build.

Fresh verification is to run in a nonroot disposable GitHubActions container, offline during checking. No local Lean/Lake execution was performed for this review. All3original proof modules and all8public `Audit.lean` targets remain included. The added4bridge declarations give12total per-group target entries. The unchanged official auditor, strict bridge precheck, source/dependency stability hashes, full target export and NaNoda replay must succeed before a passed conclusion. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted; actual used subsets must be reported. Exporter4.34 compatibility rebuild is disclosed in the shared run record.

## Target inventory

| ID | Kind | Declaration | Verification entry | Definition source when different |
| --- | --- | --- | --- | --- |
| t000 | theorem | `Erdos895.erdos_895` | `JSP000746.lean` | `Erdos895.lean` (SHA256 `456dd689b74002fc2f527a805cc75f3ffd3a01abf8ab2b19d489451419f73198`) |
| t001 | theorem | `JSP000746Sharp.witness_triangle_free` | `JSP000746Sharp.lean` | Same file |
| t002 | theorem | `JSP000746Sharp.witness_no_independent_schur_triple` | `JSP000746Sharp.lean` | Same file |
| t003 | theorem | `JSP000746Sharp.counterexamples_below_eighteen` | `JSP000746Sharp.lean` | Same file |
| t004 | theorem | `JSP000746Sharp.exact_threshold` | `JSP000746Sharp.lean` | Same file |
| t005 | theorem | `JSP000746Sharp.least_threshold` | `JSP000746Sharp.lean` | Same file |
| t006 | theorem | `JSP000746.integer_graph` | `JSP000746.lean` | Same file |
| t007 | theorem | `JSP000746.jsp_000746` | `JSP000746.lean` | Same file |
| t008 | bridge | `Verify746.intended` | `JSP000746/VerificationBridge.lean` | Same file |
| t009 | bridge | `Verify746.bounded_positive` | `JSP000746/VerificationBridge.lean` | Same file |
| t010 | bridge | `Verify746.exact_finite_threshold` | `JSP000746/VerificationBridge.lean` | Same file |
| t011 | bridge | `Verify746.witness_edge_list_length` | `JSP000746/VerificationBridge.lean` | Same file |

Bootstrap-retrieved upstream definitions are not tracked project files in the selected commit. The official auditor therefore uses the unchanged tracked project entry that imports each exact declaration; the manifest separately preserves the actual definition path and its pinned port hash. The unchanged original verifier still compiles and kernel-replays every upstream module. This entry routing changes neither the checked theorem nor the selected proof source.

## Administrative conditions

This semantic assessment is not organizer approval, accepted solver registration, identity verification, merge or an award decision. The current catalog's Lean/eligibility statuses remain organizer-controlled. Existing PRs predate the revised pre-opening skill-check requirement: later checks cannot establish the historical pre-opening condition. Keep that declaration and the merged-PR claim declaration unchecked. Update the existing claim rather than silently asserting an exception or creating a duplicate.

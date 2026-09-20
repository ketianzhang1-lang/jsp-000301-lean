# JSP-000388 / Erdős 477 — semantic and source review

Preparation-stage conclusion: **证据不足 / execution not yet completed**. Static review finds a complete affirmative statement for the original existential polynomial-tiling question at `a9eae7a01edade3d5d9a386144dcd2848b4de917`; the current batch must still freshly compile and audit that exact revision. This memo is not a claim of fresh execution success. The final report must replace the execution judgment only after inspecting the actual evidence.

| Required judgment | Preparation-stage answer |
| --- | --- |
| Is the proof object the original problem? | Yes: integer polynomial, degree at least two, unrestricted integer complement, unique pair of summand values for every integer. |
| Has this batch actually verified the selected commit? | Not yet; the final execution receipt is required. |
| Does the formal endpoint cover the entire original question? | Yes at the statement/proof-structure level; its unconditional sixth-power construction supplies the existential witness. Final validation depends on the recorded checks. |
| Does it satisfy the requested Lean completeness review? | Temporarily unconfirmed until all fresh checks finish. Organizer acceptance and award eligibility are separate. |

## Exact source and original statement

- Selected own repository: [ketianzhang1-lang/jsp-000301-lean](https://github.com/ketianzhang1-lang/jsp-000301-lean), branch `jsp-000388-quadratic-obstruction`, commit `a9eae7a01edade3d5d9a386144dcd2848b4de917`, project `projects/jsp-000388`.
- Literal original question: [Formal Conjectures statement at cd0084c96ac8764cac2c4dcb1b6f1815112f1155](https://github.com/google-deepmind/formal-conjectures/blob/cd0084c96ac8764cac2c4dcb1b6f1815112f1155/FormalConjectures/ErdosProblems/477.lean), `erdos_477`, immediately following the original-question docstring. This is a specification reference, not an accepted proof; its `sorry` placeholders are not imported. Direct erdosproblems.com access returned HTTP 403; no inaccessible page is represented as having been read.
- Exact own endpoint: [`JSP000388.jsp_000388`](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/a9eae7a01edade3d5d9a386144dcd2848b4de917/projects/jsp-000388/JSP000388Complete.lean).
- Main affirmative dependency: [Erdos477.erdos477_sixth_power at upstream 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos477.lean). Its public mathematical source is Liam Price (GPT 5.6 Sol Pro), [Large Powers Tile the Integers](https://www.overleaf.com/read/whnsywnmykqm#4b6ba0); the earlier general greedy criterion is credited to [Pengbinghui/pipeline-math](https://github.com/Pengbinghui/pipeline-math/blob/main/papers/tiling-complement.pdf). Authorship here follows the inspected source header, not an assertion that every linked exposition was independently downloaded in this batch.

The original question is existential. An integer polynomial `X^6` with the required tiling suffices. It does not ask for a classification of every polynomial degree or for the cubic variant. The formal-conjecture file's additional monomial variant is also refuted by this witness, but no proof for every higher even exponent is claimed.

The own endpoint uses `Polynomial.degree`, including the degree-at-least-two condition; it does not merely assert an arbitrary integer function tiles. `Set.range f.eval` identifies summand **values**. Even powers are not injective on integer inputs, and the theorem deliberately does not assert unique polynomial inputs. Membership in a cartesian product and the `∃!` quantifier produce existence and uniqueness of both summand values. No finiteness restriction on A, sign restriction on the represented integer, or extra existence/counting hypothesis is supplied to the final theorem.

## Statement bridges and complete coverage

The auditor-owned `Verify388.Tiles` uses the literal bounded unique-pair formulation, independently of `ExactComplement`. Its five fresh bridge targets are:

1. `tiles_iff`: exact logical equivalence with the submitted complement predicate.
2. `original`: an actual integer polynomial of degree at least two solving the original question.
3. `sixth_power`: the full integer sixth-power value set, including negative inputs and all represented integers.
4. `every_integer_translate`: every constant translate `X^6+C(c)` for every integer c.
5. `quadratic_obstruction`: all nonzero leading coefficients a and b divisible by a, including b=0 and either sign of a.

These augment all 18 targets from the selected `AuditComplete.lean`, for **23 audited target entries**. The two upstream final declarations use tracked `AuditComplete.lean` as their verification entry; their actual definition file and ported SHA-256 are recorded separately. This does not mislabel downloaded upstream files as tracked own proof source.

## Completeness and trust review

The original verifier recursively compiles 155 pinned upstream modules plus `JSP000388`, `JSP000388Complete` and `AuditComplete`, treating warnings as errors. It then audits all 18 original closures, replays the imported kernel environment and two own modules, verifies all nine actual dependency revisions, rejects the false arithmetic control, and confirms stable source hashes. Run it without `--resume`; the runner must remove the project build before the fresh invocation.

Pinned toolchain is Lean 4.34.0; Mathlib is `5ed2965256430c3649e86755f9576b54eca72435`. `UPSTREAM.json` fixes original URL, Git blob, original SHA-256, compatibility transformations and ported SHA-256 for every source. Seventeen of 155 source files have recorded compatibility changes. These are syntax/API/proof-script adjustments, not mathematical assumptions. The official audit, bridge/kernel replay and independent exporter/NaNoda checks must use the same selected closure. Standard possible axioms are `propext`, `Classical.choice` and `Quot.sound`; the actual per-target sets must come from logs, not this expected allowlist.

The original `plby/lean-proofs` checkout is **not a second selected proof version in this batch**. The actual target is the own a9eae7 revision with its recorded Lean 4.34 port. The PR's old JSON incorrectly presented both repositories as selected proofs while the evidence concerned the integrated port. The replacement moves the upstream revision into explicit dependency and authorship disclosure, retaining full attribution without claiming an original upstream checkout was reproduced.

## Contribution, source history and licenses

The original own quadratic module is byte-identical to the file at `c32d8195dc69e19d9bcf96987543f306c71749f2`; direct `git show` comparison confirms SHA-256 `19c18f800c45a7aa7a7a3bd73eeaab3de4afd17acbab20cddbbfa5541883be78`. Its separately implemented explicit-difference and boundedness proof is retained. New own work is the predicate interface, general translation theorem, shifted-polynomial consequences and integration/verification. The obstruction is not the source of the affirmative sixth-power proof.

Mathematical attribution remains with Milan Sekanina (square obstruction), AlphaProof and Sarosh Adenwalla (quadratic obstruction), and the credited even-power construction authors. The upstream affirmative formalization identifies Codex as formal author. The applicant `ketianzhang1-lang` discloses OpenAI ChatGPT/Codex assistance and requests assessment only of the identified additional contribution, with no first-formalization or imported-authorship claim.

Original headers and the upstream license notice must remain. Own project license is MIT; upstream sources retain Apache 2.0 notices and their compatibility transformation record. Any distributable evidence containing source copies must also include the full Apache 2.0 license. Mathematical papers need citation, not wholesale inclusion in the evidence package.

## Current intake and unresolved official prerequisites

The inspected PR #343 is open and unmerged. Its current diff modifies only the Lean-proof and attribution fields of one catalog entry; the proof is proposed as Pending verification. Related PR #61 is closed and withdrawn from full-solution intake (quadratic scope only); PR #1129 is open and describes finite value checks; PR #1429 is open and records the existing complete upstream proof while disclaiming recorder authorship. These records must remain disclosed; this review does not certify them.

The new PR draft supplies every current formal-statement/proof/reproduction/verification field. The existing claim #1475 gains the required merged-PR field, marked still pending. It references the PR for technical proof evidence rather than duplicating a separate verification submission. Solver registration, identity review, PR merge, and the original PR's pre-opening self-check timing cannot be truthfully marked complete by editing text. No historical self-check date or priority anchor is backdated.

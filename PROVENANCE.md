# Provenance and contribution limits

The mathematical seed and sparse-square phenomenon are known. Credit for the explicit seed belongs to Don Coppersmith and James H. Davenport; the earlier sparse-product idea is classical, with Rényi and Erdős among the cited contributors. The primary 1991 paper was inspected, including the explicit formula on p. 86.

This Lean implementation was prepared in September 2026 for GitHub user `ketianzhang1-lang`, with OpenAI Codex generating the code, conducting source searches, repairing compilation errors, checking statements and assembling evidence. It is not represented as unaided manual authorship by the account holder. The user requested assistance seeking prize credit. Any recipient recommendation should use the placeholder `RECIPIENT-JSP-000393-KZ-A` until confirmation under the Prize rules.

The main proof file was written for this project. It uses the pinned Mathlib library and does not copy or import the existing plby/lean-proofs implementation. Python multiplication was used to calculate the displayed coefficients during development; it is not a trusted premise because Lean independently proves the polynomial identities. No external result was introduced as an axiom.

The earlier official registration in issue #44 and its original mathematical/formalization credits are preserved. No first solution, first Lean proof, sole authorship of the mathematics, award level, payment amount or entitlement is claimed.

Local execution required a compatibility shim for this environment's process filesystem: only the calling process's own `/proc/<PID>/exe` lookup was mapped to the supported `/proc/self/exe` alias. It did not change proof checking or expose another process. The shim is not a project dependency and is not included in the public proof or GitHub workflow. Local checking is submitter-generated evidence; clean GitHub CI and any independent review are separate.

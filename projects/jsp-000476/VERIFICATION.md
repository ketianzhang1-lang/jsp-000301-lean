# Verification record

Remote verification completed successfully on 2026-09-17.

- Tested source commit: `f633b03a38750049758fb67c2f0800bda3c42107`.
- [Successful workflow run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35173027153), job `105048572235`.
- Lean 4.34.0; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
- Build with warnings as failures: passed.
- Lean's bundled `leanchecker`: passed.
- All 20 project declarations passed the transitive axiom allowlist:
  `propext`, `Classical.choice`, `Quot.sound`.
- Prime, composite-squarefree, equality-boundary, and square-factor examples compiled.
- Every fetched dependency revision matched the committed manifest.
- All 1,664 independent finite subset-sum checks passed.
- The negative control `1 = 0` was rejected as expected.
- Source and verification artifact upload: successful.

The proof source SHA-256 is
`543e9c46142bd9fa8092f1fbdc34c4648cebe0b9e595c1ea045db9b72ae4f67e`.

The exact contiguous verification-step log is archived as
[evidence/ci-verification.log](evidence/ci-verification.log), SHA-256
`1dfec36b6fbd2267dd580439b9aad8d9a310061788e74a7b388c8379f3f8dbf4`.
[evidence/ci-verification.json](evidence/ci-verification.json) records the source
binding, complete job step outcomes, and artifact digest.

GitHub artifact `10477641570` (`jsp-000476-evidence`) contains the source archive
and individual logs. Its reported archive digest is
`sha256:1f5fe698978e9482d659ae5d673d743917c107c3e9903bf46fa8319e5af8e13c`;
its reported expiry is 2026-12-16. The retained textual excerpt and JSON record
do not depend on that artifact remaining available.

This evidence commit changes documentation and evidence only. The checked Lean
source and build scripts remain identical to the tested source commit above.
The local cached-toolchain checks were also successful; the remote run supplies
ordinary-toolchain reproduction and dependency-revision provenance.

The bundled checker belongs to the Lean toolchain; no separate NaNoda verification
or independent mathematical peer review is claimed. Successful verification
establishes the stated family-level theorems, not originality, completeness for
JSP-000476, or prize eligibility.

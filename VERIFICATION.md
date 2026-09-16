# Verification evidence — JSP-000301

## Evidence scope

This report records observed contributor-controlled CI results, not an official Prize verification record or an independent human review.

Verified proof snapshot: `e1a17b0d6728b9d4929d1d4abd3721a27377369a`.

- Repository: https://github.com/ketianzhang1-lang/jsp-000301-lean
- Pinned source: https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/e1a17b0d6728b9d4929d1d4abd3721a27377369a/JSP000301.lean
- Pinned manifest: https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/e1a17b0d6728b9d4929d1d4abd3721a27377369a/lake-manifest.json
- Full verification run #13: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35131699133
- Job ID: `104914009901`; completed successfully on September 16, 2026, approximately 18:05:47 UTC.
- Earlier successful run #12: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35130895580 (commit `b45708ccb84915115bffef995c547a011a4e0131`). Its generated manifest was committed and rechecked in run #13.

## Observed checks in run #13

| Check | Observed result |
| --- | --- |
| `lake build --wfail` | Successful, including a fresh `JSP000301` compilation; 815 build jobs in the dependency graph. |
| Bundled `leanchecker JSP000301` | Successful exit. |
| NaNoda v0.4.17 | 188,335 declarations checked; no typechecker errors. |
| Separate project axiom-audit | 9 declarations under `JSP000301`; all within `[propext, Classical.choice, Quot.sound]`. |
| Dependency manifest upload | Successful. |

NaNoda also emitted one pretty-printer error: `Unable to print axioms`. Its typechecking exited successfully; this report does not describe the entire run as error/warning-free. A separate axiom-audit subsequently completed successfully. There were also runner/tool deprecation messages.

The NaNoda whole-environment allowlist includes `Lean.trustCompiler`, as in the upstream integration. Its unpermitted-axiom setting skips unused declarations but rejects dependencies on disallowed axioms. The **project** axiom-audit is stricter and allows only the three foundational axioms above. No project dependency on `sorryAx`, custom axioms or native-evaluation axioms is claimed or permitted by that project audit.

## Version pins

| Component | Version / commit |
| --- | --- |
| Lean | `v4.34.0`; `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` |
| Mathlib | `v4.34.0`; `5ed2965256430c3649e86755f9576b54eca72435` |
| lean-action | `50fcf42d2e460296f1a34b402e990d1b24f8b596` |
| lean4export | `6cea97789dc088ea47fcea15692db85685aedac5` |
| NaNoda | `4c544ed4099c8227f07d5de77ad1e69fb0740a27` |
| axiom-audit | `v0.1.2`; `46024e005996495c65ef609368e11ab39c4222e3` |

The manifest records all transitive library revisions. The workflow patches only the upstream checkout commands to pin compatible exporter and NaNoda revisions; checker semantics are unchanged. The earlier stale NaNoda parser was discussed in [lean-action PR #177](https://github.com/leanprover/lean-action/pull/177).

## Artifact evidence

The uncompressed manifest has SHA-256:

`24f2acc41ac6d5ed37e75941cdde09c76c829943a0e5008b1fd22084dfdb8b9a`

Run #12 manifest artifact: ID `10461562204`, ZIP size 828 bytes, ZIP SHA-256 `67e0656f8c21ac48ef670a7711b8d1b63b97091dd6974035b3d8346a30608d43`.

Run #13 manifest artifact: ID `10461443614`, ZIP size 828 bytes, ZIP SHA-256 `c156d8c61cbab5ca9a7b539bbfa078d4fc53e3c4781b2cb17f65bd941c3ae04c` (as reported by the upload log).

CI artifacts have retention limits. The manifest is also permanently addressable in the pinned Git commit while the repository remains available. Different ZIP hashes need not imply different manifest content because archive metadata can differ.

## Reproduction and limits

Use the commands in README.md at the exact verified commit; the workflow provides all external-checker commands. `lake update` is not part of locked-snapshot reproduction.

The runs used fresh GitHub-hosted Ubuntu runners with network access and official precompiled Mathlib cache files. Restoration of this repository's `.lake` cache was disabled in runs #12 and #13. This is **not** a claim to have rebuilt all dependencies from source or to have performed the Prize's official isolated offline verification.

The Lean build and bundled leanchecker share a kernel implementation; NaNoda is a separate checker implementation, but all tools here were operated within the contributor's workflow. Independent human statement fidelity review, current-safe-version approval, priority adjudication and official recipient confirmation remain pending. The compiled source contains no `sorry`, `admit`, `native_decide` or added axiom declarations.

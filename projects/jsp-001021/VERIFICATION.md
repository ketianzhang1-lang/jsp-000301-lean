# Verification record

## Selected proof and completed local checks

- Proof branch: `jsp-001021-tournament-verification`.
- Selected proof commit: `7642a7f5eb190da6319b6ae7f11c829d7737e2dd`.
- All four source modules compiled with Lean 4.34 and warnings treated as errors.
- All four modules passed Lean's bundled kernel replay.
- The exact fifteen-vertex and universal-negation types passed their checks.
- All eleven audited theorem closures use only `propext`, `Classical.choice` and `Quot.sound`.
- All nine dependency revision checks and the false-arithmetic negative control passed.

The local checks ran during preparation of the published commit. [The machine-readable record](evidence/local-verification/verification.json) preserves the actual local repository HEAD at that time and SHA-256 hashes of every checked input. [The source binding](evidence/local-verification/source-binding.json) records the selected public commit and the successful byte comparison with its published project inputs; bootstrap separately binds the two upstream modules to `UPSTREAM.json`. The old local HEAD is not being presented as the proof version for review.

[Public GitHub Actions run 35279395960](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35279395960) is a separate reproduction at the exact selected proof commit. Its live status is authoritative. This receipt records the completed local checks and does not assert a successful public run before it finishes.

## Reproduce and interpret the checks

`bash scripts/verify.sh` compiles the two pinned upstream modules, `FiniteChecks.lean` and `JSP001021.lean`, replays all four modules, checks the exact fifteen-vertex and universal-negation statements, audits eleven theorem closures, checks actual dependency revisions and rejects an invalid arithmetic statement.

The workflow preserves logs and source hashes under `evidence/generated/` and archives the executed repository commit. Contributor-run builds use network access and Mathlib caches; they are not independent human certification or a fully offline dependency rebuild. The local certificates establish the exclusions stated in their theorem, while the full main theorem uses the attributed fourteen-vertex proof.

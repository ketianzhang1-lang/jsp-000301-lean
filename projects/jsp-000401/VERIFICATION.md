# Verification record — 2026-09-17

## Tested source and public run

Proof commit: `096288b2f397e11772e15deda80c3b277247b6e4` in `ketianzhang1-lang/jsp-000301-lean`.
Directory: `projects/jsp-000401`.

Successful public run:
https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176557771

Job: 105059438857. Every job step completed successfully. The workflow compiled the proof under pinned Lean 4.34.0 and Mathlib with warnings as errors, replayed it with the bundled Lean checker, passed all nine target axiom audits and all nine dependency-revision checks, and rejected the false-arithmetic control. The build completed successfully with 971 jobs.

Permitted foundational axioms: `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`, native-evaluation, or compiler-trust axiom is allowed by the audit. The universal endpoint is `JSP000401.turan_lower_bound`.

The independently implemented NaNoda checker successfully checked **6,497 declarations with no errors**, covering the dependency closures of the endpoint and the total-incidence theorem. The exporter and checker are pinned in `scripts/verify_nanoda.sh`. This is contributor-run independent-software verification, not independent human review or organizer certification.

A selected verbatim log excerpt is in `evidence/CI_EXCERPT.txt` in the submission package. The full logs and source archive are in the workflow artifact.

## Artifact and limitations

GitHub-reported artifact ID: 10478576390.
Name: jsp-000401-evidence.
Size: 4,351,620 bytes.
Reported ZIP SHA-256: c1a7f1e0e829539a914295fbc7db21516b2d156994d312804fdf013fa18a0d1a.
Advertised expiration: 2026-12-16T03:00:50Z.

The ZIP digest is GitHub-reported; a separately downloaded local ZIP digest is not claimed. Artifact retention is finite. Source is preserved at fixed commits; permanent independent archival of the complete exported evidence remains pending. Cached Mathlib and network access were used. No full offline dependency rebuild, independent human sign-off, official safe-version approval, or payment authorization is claimed.

## Submission fidelity and repository checks

The Lean source, Audit.lean, toolchain, manifest, lakefile, and both checking scripts in the submission package are byte-identical to the tested proof package. Documentation and this receipt have been updated after the run to record the outcome.

All 22 existing official repository tests passed. `manage.py validate`, `links`, `build`, `check`, and `history` against `f4e7173d89dfe91022a185427d63452c8ffbf6ae` passed. Final documentation link and generated-data checks also passed. No pre-existing catalog, candidate, award, recipient, schema or validator record is modified.

These checks support reproducibility and statement inspection; they do not determine priority or eligibility for an award.

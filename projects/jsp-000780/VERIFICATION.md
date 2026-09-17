# Verification

## Completed local checks

On 2026-09-17 UTC, under Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`:

- `lake build --wfail`: passed, both project modules (3,094 build jobs).
- Bundled `leanchecker`: passed for `JSP000780` and `Audit`.
- Six named target axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
- All nine package revisions match `lake-manifest.json`.
- False arithmetic negative control: rejected, as required.

Exact hashes and outcomes are in `evidence/local-verification.json` and
`evidence/SOURCE_SHA256SUMS`; actual logs are in `evidence/`.
The kernel replay commands are silent on success; their exit codes are recorded.
The quantified proof establishes infinitude; no finite computation is used as
a substitute for that proof.

The local runtime used official cached dependencies and a filesystem readlink
compatibility shim that maps only `/proc/<own PID>/exe` to `/proc/self/exe`.
No Lean kernel, proof or checker code was altered. This is not an offline
full-library rebuild or an independent checker run. A clean hosted CI job
and the pinned NaNoda check are prepared separately; their presence is not a
claim of successful execution.

## Review still needed

Statement fidelity, attribution, prior-work overlap, partial-scope eligibility,
minimum-safe-version approval, human independence and recipient confirmation
remain for the organizers to assess. These are contributor-run checks.
No award decision or permanent external archival is claimed. Workflow artifacts
have finite retention, while source and compact logs are committed to Git.

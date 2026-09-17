# Contributor-run verification

On 2026-09-17, [GitHub Actions run 35168402594](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168402594)
completed successfully on Ubuntu 24.04. The checked proof commit is
[`7b545f0e021b06d434654b17881c11819f3ff1b7`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/7b545f0e021b06d434654b17881c11819f3ff1b7/projects/jsp-000925-strict).
The original submission copied twelve reproduction/source files from that directory.
The current Lean source, dependency configuration and scripts remain byte-identical
to the checked proof. This receipt, archived logs and later documentation updates
do not alter the checked proof.

## Results

| Check | Result |
| --- | --- |
| Checksum-pinned upstream prerequisite | Passed; 68,673 bytes |
| `lake build --wfail` | Passed; 8,926 build jobs including cached dependencies |
| `leanchecker Erdos1114` | Passed, exit 0; checker is silent on success |
| `leanchecker JSP000925Strict` | Passed, exit 0; checker is silent on success |
| Eight target and helper axiom audits | Only `propext`, `Classical.choice`, `Quot.sound` |
| All Git dependency revisions against the manifest | Passed |
| False arithmetic control `1 = 0` | Rejected with the expected diagnostic |
| NaNoda export of both main theorem dependency closures | 50,927 declarations checked, no errors |

The exact theorem and predicate renderings are in
[nanoda-statements.txt](verification/nanoda-statements.txt), with
[axiom output](verification/axioms.log), [build output](verification/build.log),
[NaNoda result](verification/nanoda.log), [negative control](verification/negative.log),
and the [complete Actions job log](verification/github-job.log).
The two kernel logs are empty because those successful commands emitted no
output. They execute sequentially under `set -euo pipefail` before the later
audits, and the containing Actions step succeeded.

## Version and source binding

- Lean 4.34.0, release commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435`; transitive pins in
  [lake-manifest.json](lake-manifest.json).
- `lean4export` at `6cea97789dc088ea47fcea15692db85685aedac5`, built with this Lean toolchain.
- `nanoda_lib` at `4c544ed4099c8227f07d5de77ad1e69fb0740a27`, built with `cargo build --release --locked`.
- NaNoda uses a hard-error axiom allowlist containing exactly the three standard
  axioms above; natural-number and string reduction extensions are enabled.
  See [the complete configuration](verification/nanoda-config.json).
- Supplement SHA-256: `ae35fbe83a0d5fba85e0e223907fff3bc1b0cdd6fb4b7245c02c0ba4e9fe3c31`.
- Upstream prerequisite SHA-256: `570e485a1548dd090451dc095ed1ed1128806631e1abff4893405f3e42ea1825`.

[SOURCE_COMMIT](verification/SOURCE_COMMIT) and
[SOURCE_SHA256SUMS](verification/SOURCE_SHA256SUMS) came directly from the run.
Those source hashes identify the executed proof snapshot; they are not checksums of later README or provenance revisions.

## External artifact

The [original evidence archive](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168402594/artifacts/10475571672)
contains the compressed exported proof closure and all fifteen original evidence
files. Its download was independently checked against the reported size and
SHA-256:

- Artifact ID: `10475571672`; name: `jsp-000925-strict-evidence`.
- ZIP size: **53,524,136 bytes**.
- ZIP SHA-256: `bb353673593c587c1770d8f4d4aa96dbc958f266aef195923a5c12618c268534`.
- Created: `2026-09-17T00:58:51Z`; advertised expiration: `2026-12-16T00:54:01Z`.

The Actions archive is retention-limited and downloading may require GitHub
sign-in. All compact evidence files are preserved in this submission; only
`export.ndjson.gz` is omitted from the Git diff. Its original hash remains in
[CHECKER_SHA256SUMS](verification/CHECKER_SHA256SUMS), and the pinned scripts can
regenerate it. This is not a claim of permanent archival storage.

## Historical repository checks and verification limits

Against awards base `f4e7173d89dfe91022a185427d63452c8ffbf6ae`, all 22 existing
validator tests passed. `manage.py validate`, `links`, `build`, `check`, and
`history --base` also passed. The [local preflight log](verification/awards-preflight.log)
records these separate structural checks. Generated JSON did not change.

Lean elaboration and `leanchecker` share Lean's kernel. NaNoda is a separately
implemented checker, but its input is produced by the pinned Lean exporter;
this does not eliminate trust in the toolchain, exporter, checker, hardware, or
the choice of formal statement. CI obtained dependencies over the network and
used the Mathlib cache; no fully offline rebuild of every dependency is claimed.

These are contributor-run checks, not independent human review, organizer
certification, a prize decision, or permission to pay. The catalog currently
marks the entry ineligible to claim. See [README.md](README.md) for the complete endpoint, our concrete additions and requested contribution review.

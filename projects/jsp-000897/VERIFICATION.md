# Verification receipt — 2026-09-17 UTC

## Immutable tested source

Commit: `914c6fa28200985d6409b5b34588b9f5c4a87d00`.

Source: https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/914c6fa28200985d6409b5b34588b9f5c4a87d00/projects/jsp-000897

Successful run: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178602861

Job: `105065702988`. All steps completed successfully. Later receipt-only changes do not change the tested Lean sources, dependency pins or verification scripts.

## Actual results

| Check | Result |
| --- | --- |
| Lean v4.34.0, `lake build --wfail` | Passed, 3,123 build jobs |
| Lean kernel replay of Erdos1079 | Passed |
| Lean kernel replay of JSP000897 | Passed |
| Eight typed axiom audits | All list only propext, Classical.choice, Quot.sound |
| All nine dependency revision checks | Passed |
| Invalid arithmetic negative control | Rejected, as required |
| Independent NaNoda checker | 11,259 declarations checked with no errors |
| Official repository validation, links, build, check and history | Passed |
| Official repository unit tests | All 22 passed |

The exact upstream source bytes were compared with the GitHub contents response for the pinned upstream commit and matched. The retained upstream original targets 4.33.0; the ported main file targets 4.34.0. See PROVENANCE.md for the changes.

The compiled library source files, Audit.lean, dependency manifests and both checking scripts are byte-identical between the tested commit and this review package. Documentation and receipts are updated after checking.

## Pinned tools

- Lean: `leanprover/lean4:v4.34.0`.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
- lean4export: `6cea97789dc088ea47fcea15692db85685aedac5`.
- NaNoda: `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.
- All transitive package revisions: lake-manifest.json.

NaNoda exported and checked both full classical endpoints and all four supplement endpoints with their dependency closures. Only the three listed foundational axioms were permitted; all other axioms were configured as hard errors.

## Evidence archive

GitHub artifact: `jsp-000897-evidence`, ID `10479034803`.

- GitHub-reported ZIP size: 7,995,766 bytes.
- GitHub-reported digest: `sha256:5346d087b269abb1824025397c252cc623723e733ed7ea3e7ad22e80f5251410`.
- Expiry: `2026-12-16T03:33:19Z`.
- Accessible from the linked successful run.

The archive contains build, kernel, audit, negative-control and NaNoda logs, the compressed exported proof closure, checker configuration, source archive and hashes. Selected public job-log lines are retained in evidence/CI_EXCERPT.txt.

The ZIP was not independently downloaded and hashed in this session. Its size and digest above are GitHub API metadata. The source files and scripts are retained in Git independently of the artifact's finite retention period.

## Limits

Official compiled dependency caches were used. This is contributor-run machine verification, not a complete offline dependency rebuild, independent human review, an organizer verification signature or award approval. Leanchecker uses Lean's own kernel implementation; NaNoda is the separately implemented Rust checker.

A complete earlier formalization exists and is credited. Recognition of the port, explicit surplus supplement and verification evidence requires organizer review; successful checking does not establish originality or a payment entitlement. The exact problem webpage returned HTTP 403, so original-statement correspondence remains an explicit review item alongside the catalog and pinned formal specification.

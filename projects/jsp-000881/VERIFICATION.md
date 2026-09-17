# Verification status

Prepared 2026-09-17 UTC.

## Completed locally

- The complete mathematical source was elaborated using Lean v4.34.0's
  `Lean.Elab.runFrontend` with trustLevel=0. Final run exited 0 without warnings.
- All ten source-level target axiom inspections completed, each reporting
  only propext, Classical.choice and Quot.sound. Typed restatements of the main
  bounds and the S(0)=0, S(3)=2 boundary checks also passed in the same run.
  The actual output is preserved in evidence/local-axioms.log.
- A separate Python divisor sieve exhaustively counted all ordered solutions
  at N=270,540,810: 286,742,1228, respectively. Constructed witness counts were
  76,152,228. All witnesses were valid and distinct. These finite checks are
  sanity checks only; the all-N assertion is established by Lean.

## Completed cloud reproduction

- Workflow: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176439458
- Tested source commit: `bad12390f362ae74b0c825256824b9fdaf897136`.
- Job ID: `105059085248`; conclusion: success.
- `lake build --wfail`: success (3,095 jobs, including cached dependencies).
- `leanchecker JSP000881` and `leanchecker Audit`: success.
- All ten target axiom audits: only propext, Classical.choice and Quot.sound.
- All pinned dependency revisions matched the manifest.
- The deliberately false arithmetic negative control was rejected.
- Independently implemented NaNoda: **9,711 declarations checked with no errors**.
- Exporter revision: `6cea97789dc088ea47fcea15692db85685aedac5`.
- NaNoda revision: `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.
- Complete public job log: `evidence/cloud-workflow.log`.
- Source-file hashes: `evidence/SOURCE_SHA256`.

### Evidence archive receipt

The GitHub Actions API reports:

- Artifact ID: `10478299661`, name `jsp-000881-evidence`.
- Size: `6,398,179` bytes.
- SHA-256: `33068f7f34f208a7887f6147a931c5804b9e15cf73ea78134bb3978fe7560948`.
- Expiry: `2026-12-16T02:58:58Z`.
- Archive page: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176439458/artifacts/10478299661

The API receipt is recorded, not represented as an independent local hash
recomputation. The connector supplied a download reference, but a subsequent
local transfer returned HTTP 403; no successful local ZIP extraction is claimed.
The source, scripts, hashes and full text workflow log are preserved in the
repository. The large proof-export archive is subject to the stated retention,
not represented as a permanent external archive.

This report and additional logs were added after the successful run; the tested
mathematical source, audit, dependency manifest and verification scripts remain
byte-identical to the tested commit.

## Limits

No proof of the full open conjecture, independent human mathematical review,
designated organizer approval, award decision, or payment is asserted.
Dependency caches are used; a from-source rebuild of the entire toolchain and
Mathlib is not claimed. Lean's bundled leanchecker is the same kernel
implementation; NaNoda is the separately implemented check when completed.

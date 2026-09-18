# Executed verification of JSP-000585

The complete proof at commit **`9661ef0f170e750b1ac2153b9017bad86044680c`** passed the
[public workflow run 35332110641](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35332110641). The run's head SHA
matches this proof commit on branch `catlin-sharp-kz`.

## Checks actually passed

- **66 modules** compiled with warnings treated as errors: 56 pinned upstream
  sources, seven unchanged original modules, two new modules and the audit.
- **61 theorem-closure axiom audits** passed, covering all 60 public theorems
  in our original/new modules and the complete imported general upper theorem.
- Only `propext`, `Classical.choice` and `Quot.sound` occur in those closures.
  No sorryAx, compiler-trust axiom or added custom axiom occurs.
- Lean kernel replay passed for all 56 upstream modules and all nine of our
  proof modules, through ten module/prefix replay invocations.
- All nine actual dependency revisions match the committed manifest.
- Original-source and compatibility-port hashes are pinned for all 56 inputs.
- The false statement `1 = 0`, with the complete development imported, was
  rejected as expected.
- **NaNoda checked 48,436 declarations with no errors**
  for the full exported dependency closure of all 61 selected targets. Any axiom
  outside the three-name allowlist is a hard error; target statements were
  also printed successfully.

The separately implemented checker is NaNoda at
`4c544ed4099c8227f07d5de77ad1e69fb0740a27`; lean4export is pinned at
`6cea97789dc088ea47fcea15692db85685aedac5`. Leanchecker itself reuses Lean's
kernel and is not an independent kernel implementation.

## Reproducible inputs and receipts

Use Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435` with
the committed nine-package manifest. [README.md](README.md) contains commands.
[UPSTREAM.json](UPSTREAM.json) records original immutable source URLs, Git blob
hashes, SHA-256 hashes, exact compatibility edits and resulting source hashes.
The bootstrap fetches source for the general upper proof, not prebuilt proof
objects; the Mathlib cache remains a pinned dependency.

All seven original Catlin modules remain byte-identical to commit
`019467ead20f2d6b87e672a1dfef7d5b8886febf`. Their hashes are preserved in the
receipt alongside the complete proof source hashes. Our new model bridge and
extremal endpoint connect this original proof to the attributed general result.

[Public CI log](verification/public-ci.log) and
[receipt](verification/public-ci-receipt.json) record the hosted result and exact
proof commit. The receipt includes the workflow artifact ID, size, API-reported
digest and retention date. The digest is GitHub's report, not a locally
recomputed ZIP hash. The workflow archive holds source, verification logs,
exported declarations, checker configuration and printed statements. Hosted
artifacts expire; the committed log and receipts remain accessible.

[Local verification record](verification/verification.json),
[axiom reports](verification/axioms.log), adjacent replay logs,
[negative control](verification/negative-control.log) and
[local transcript](verification/local-verification.log) record the local pass.
Local compilation resumed successful hash-matched builds; the hosted run
compiled every module without resume. The local record's preparation HEAD
identifies the original checkout, while its source hashes identify the newly
completed files. Older evidence/local-build.log and evidence/local-axioms.log
refer only to the earlier finite proof.

This receipt revision follows the tested proof commit. All 66 proof source
hashes are unchanged. Automated contributor-run verification does not establish
independent human semantic review, organizer acceptance, contribution eligibility,
first-formalization priority or award entitlement.

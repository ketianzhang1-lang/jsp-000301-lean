# Verification of the complete JSP-000725 proof

On 2026-09-18 UTC, all **46 modules** compiled locally with warnings treated as
errors: 42 pinned upstream modules, our original construction, our bridge, our
complete endpoint, and the audit module. The original construction source is
unchanged from `a197ebc6cc3ea878c60db0f2456465cef1e8e09b`.

All **28 theorem-closure axiom reports** passed the strict allowlist
`propext`, `Classical.choice`, `Quot.sound`. These reports include every public
theorem in our three modules and both full upstream endpoints. No `sorryAx`,
compiler-trust axiom, or additional custom axiom occurs in those closures.

All nine dependency revisions match `lake-manifest.json`. All 42 upstream source
files have pinned original and ported SHA-256 hashes and original Git blob
hashes in `UPSTREAM.json`. Compatibility edits preserve theorem statements.

The complete local kernel replay and false-arithmetic control are being run
separately from compilation. Their successful completion must be established
from the resulting logs, not inferred from the checks above.

The [public workflow](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/workflows/jsp-000725.yml)
rebuilds the full proof and runs NaNoda against all 28 exported theorem closures.
NaNoda is pinned at `4c544ed4099c8227f07d5de77ad1e69fb0740a27`; the Lean exporter
is pinned at `6cea97789dc088ea47fcea15692db85685aedac5`. Only the same three
axioms are allowed, with unpermitted axioms configured as hard errors. The
workflow requires an explicit successful declaration-check report and nonempty
printed target statements. A passing run must have `head_sha` equal to the
selected proof commit; a workflow definition is not a verification result.

The source archive, complete build logs, axiom reports, replay logs, negative
control, export, NaNoda configuration and result are collected by the workflow.
Leanchecker reuses Lean's kernel; NaNoda is the separately implemented checker.
These contributor-run checks do not constitute independent human review,
organizer acceptance, or award certification.

Reproduction commands and attribution appear in [README.md](README.md).

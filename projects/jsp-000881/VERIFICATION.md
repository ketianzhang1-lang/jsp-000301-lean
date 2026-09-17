# Verification status

Prepared 2026-09-17 UTC.

## Completed locally

- The complete mathematical source was elaborated using Lean v4.34.0's
  `Lean.Elab.runFrontend` with trustLevel=0. Final run exited 0 without warnings.
- Initial source-level axiom inspections of the four main conclusions reported
  only propext, Classical.choice and Quot.sound. The separate package Audit
  target and standard build are included in CI for reproduction.
- A separate Python divisor sieve exhaustively counted all ordered solutions
  at N=270,540,810: 286,742,1228, respectively. Constructed witness counts were
  76,152,228. All witnesses were valid and distinct. These finite checks are
  sanity checks only; the all-N assertion is established by Lean.

## Cloud reproduction

Pending at this source commit. The dedicated workflow runs a standard package
build, Lean kernel replay, target axiom audit, invalid-proof negative control
and a separately implemented NaNoda replay. Do not treat this paragraph as
claiming those cloud checks have already passed. A completed workflow URL and
result will be added after the run finishes.

## Limits

No proof of the full open conjecture, independent human mathematical review,
designated organizer approval, award decision, or payment is asserted.
Dependency caches are used; a from-source rebuild of the entire toolchain and
Mathlib is not claimed. Lean's bundled leanchecker is the same kernel
implementation; NaNoda is the separately implemented check when completed.

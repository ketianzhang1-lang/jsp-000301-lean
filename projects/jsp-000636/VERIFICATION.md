# Executed verification — complete original threshold-estimate endpoint

The local verification completed successfully on 2026-09-18 UTC. The preparation
parent is `36da76e793678ee6a062f1703674fd3789334cbd`. The source and object hashes
in `verification/local-verification.json` identify the actual new work tested
before publication; the parent commit alone does not contain the new module.

## Completed local checks

- The eight-module project builds with warnings treated as errors under Lean
  4.34.0. The new `OriginalQuestion.lean` module also passed a separate explicit
  warning-as-error compilation. The local full-project build reused successful
  unchanged-module artifacts, rather than claiming an unnecessary fresh build.
- All eight proof modules pass fresh replay by Lean's bundled kernel checker.
- All **79 public theorem dependency closures** use only `propext`,
  `Classical.choice` and `Quot.sound`, or a subset; no `sorryAx`, custom axiom
  or compiler-trust axiom appears in these closures.
- All nine actual dependency Git revisions match the committed manifest.
- The false-arithmetic control importing `OriginalQuestion` is rejected because
  `(1 : Nat) = 0` is false.
- All seven inherited proof modules, `lean-toolchain` and `lake-manifest.json`
  are byte-identical to the preparation parent.

Logs, axiom reports, negative-control output and source/object hashes are in
`verification/`. `SOURCE_SHA256SUMS` binds the public project files. The earlier
asymptotic-supplement receipt is retained separately, with its historical scope.

## Hosted verification and limits

The previous 71-theorem revision passed its public build, audits, kernel replay,
negative control and independent NaNoda check in
[run 35293244855](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35293244855).
That historical result does **not** verify the eight new theorems.

The workflow for the selected new proof commit repeats the full build and
79-theorem checks, then independently exports and checks the new final endpoints
with NaNoda. Consult the exact commit's
[workflow run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/workflows/jsp-000636.yml)
for its actual result. A configured step or a running job is not a successful
check. NaNoda was not run locally because the Rust build toolchain is absent.

Compilation uses pinned cached Mathlib objects and network access. Lean kernel
replay is not an independently implemented checker; contributor-run automated
checks are not independent human review or organizer certification.

These checks establish the stated original-threshold estimates and finite-set
interfaces. They do not establish the stronger piecewise exact formula from
PR #677, priority, organizer acceptance, contribution eligibility or an award.

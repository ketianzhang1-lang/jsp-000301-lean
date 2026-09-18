# Verification receipt — asymptotic threshold supplement

The tested worktree extends `d5fc3ee7fc5a452e8104b5099c854a5a15a668bf`.
The source hashes in `verification/local-verification.json` identify the actual
new files tested before publication; `preparation_head` is the parent commit,
not a claim that the parent already contained this supplement.

## Completed local checks

- Seven modules compile with warnings treated as errors under Lean 4.34.0.
- All seven modules pass Lean's bundled kernel replay.
- All 71 theorem dependency closures use only `propext`, `Classical.choice`
  and `Quot.sound` (or a subset).
- All nine actual dependency Git revisions match the committed manifest.
- The false-arithmetic control `(1 : Nat) = 0` is rejected because it is false.
- The six inherited proof modules are byte-identical to the parent revision.

Full local logs, the axiom reports, negative control and source hashes are in
`verification/`. The older pair-label receipt is preserved separately there.
Compilation used pinned Mathlib cached objects; this is not a source rebuild
of all of Mathlib, an independent human review or organizer certification.

The local additional NaNoda attempt stopped because `cargo` is unavailable in
this environment, before running the checker. **No successful local NaNoda run
is claimed for the new module.** The public workflow requests that separate
check; its actual status is available under Actions for the selected commit.
Historical NaNoda results for the parent do not verify the new supplement.

These checks establish the stated formal estimates and interfaces. They do
not establish the stronger piecewise exact-threshold formula from PR #677,
full-scope prize eligibility, global priority, organizer approval or an award.

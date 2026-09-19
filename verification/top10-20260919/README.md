# Top ten submission verification — 2026-09-19

This contributor-run evidence bundle checks the exact 12 selected proof commits for JSP-000391, 000438 (two versions), 000925, 000250, 000636, 000912, 000393, 000728, 000585 and 000506 (two versions).

The unchanged official `lean-verify` skill and helper under `official-skill/` are copied from [TheJustinSunPrize/awards at 38e63c424c7196f8d4ceb664c5c25f0c0529d5e2](https://github.com/TheJustinSunPrize/awards/tree/38e63c424c7196f8d4ceb664c5c25f0c0529d5e2/skills/lean-verify), copyright their respective authors and governed by the upstream repository license. The separate runner and workflow record clean source rebuilds, dependency pins, kernel replay, negative controls, and target-level `#check`, `#print`, and `#print axioms` output in non-root containers. Preparation may download pinned inputs; checking has no network access. No submitted Lean source or selected proof commit is changed.

Mechanical results do **not** establish semantic correctness, official acceptance, solver registration, priority, or an award. A separate statement/coverage review and final report are required. At this initial harness commit the checks have not yet completed. No overall Verification passed result is asserted here.

The PRs predate the new verification requirement. Any completed report is a retrospective update with its actual execution date, never a claim that this workflow ran before those PRs were opened. Mathematical review, solver-candidate registration, PR merge, and subsequent award-claim processing remain subject to the official process.

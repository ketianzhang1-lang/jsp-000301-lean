# Verification record

Development date: 2026-09-17.

- `JSP000476.lean`: local compilation passed with Lean 4.34.0.
- Bundled `leanchecker JSP000476`: exit status 0.
- All 20 project declarations passed the transitive axiom allowlist:
  `propext`, `Classical.choice`, `Quot.sound` only.
- The independent Python subset-sum check passed 1,664 cases:
  all multipliers 1–128 and all lengths 0–12.
- The source contains no `sorry`, `admit`, custom axiom, or `native_decide`.

The cached local dependency directories do not expose Git commit metadata;
local checks alone therefore do not establish an independently fetched dependency
provenance. The remote workflow checks every dependency revision against the
committed manifest using a normal Lean installation. Its outcome will be recorded
separately once completed. No successful remote run is claimed here yet.

This is a partial mathematical result. Successful verification establishes the
stated theorems, not originality, completeness for JSP-000476, or prize eligibility.

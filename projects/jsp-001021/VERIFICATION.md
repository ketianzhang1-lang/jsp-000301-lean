# Verification record

This revision supplies a complete Lean dependency chain in addition to the historical Python reproduction. The proof version and fresh verification results will be identified in the linked submission after the run completes; the earlier Python output is not offered as Lean verification.

`bash scripts/verify.sh` compiles the two pinned upstream modules, `FiniteChecks.lean` and `JSP001021.lean`, replays all four modules, checks the exact fifteen-vertex and universal-negation statements, audits eleven theorem closures, checks actual dependency revisions and rejects an invalid arithmetic statement.

The workflow preserves logs and source hashes under `evidence/generated/` and archives the executed repository commit. Contributor-run builds use network access and Mathlib caches; they are not independent human certification or a fully offline dependency rebuild. The local certificates establish the exclusions stated in their theorem, while the full main theorem uses the attributed fourteen-vertex proof.

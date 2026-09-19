# Reproducing this supplemental self-check

The selected proof commits are unchanged. Do not substitute a branch tip or run `lake update`.

The checked workflow is `lean-verify-rank34.yml`; `harness/config.json` identifies each proof checkout. The complete official skill is included in each raw artifact under `official-skill/`. The official audit script is unchanged, SHA-256 `5db45dddcb4d588bc27e7c7161fbca5cedaa3e73e1c40843d21f5a214323cd07`.

1. Fetch the exact submitted proof commit and confirm its ancestry in the stated branch.
2. Read the fixed statement and the report's obligation matrix. Review definitions and quantifiers independently of the target names.
3. Use the pinned Docker harness to bootstrap upstream sources, retrieve the trusted dependency cache and build pinned external checkers. Keep the prepare and offline verification stages separate, as in the workflow.
4. Run the original clean verifier. For JSP-000250, `lake build` alone does not build the complete lower proof: `bash scripts/verify.sh` invokes the explicit 78-module compiler/checker driver. Do not use its optional resume mode for a fresh reproduction.
5. In the isolated project, run official `audit.py preflight` and `audit.py run` with the exact manifest. The script explicitly checks target modules, source files, declarations and transitive axioms.
6. Replay original modules and independent audit bridges with Lean's checker, export all target closures and run pinned NaNoda. Examine the negative controls and every exit code, not just the workflow badge.
7. Compare input hashes and actual dependency revisions. Preserve raw artifacts without editing them, then write semantic conclusions in a separate report/reviewed manifest.

The raw executed manifests retain `coverage: pending`; that is intentional. Semantic coverage is established in the report and post-review manifests, not by the automatic script.

Changing any selected proof commit requires a new full check for that version. Updating PR prose does not change the proof commit. This supplemental date cannot retroactively satisfy the literal assertion that the check occurred before an existing PR was opened. Maintainers must resolve that procedural question and the solver-registration prerequisite; claims must not assert a merge that has not occurred.

The copy page supplies English title/body replacements for the existing two PRs and two claims. Edit those existing threads rather than creating duplicate claims. Official repository write access was unavailable; supplying these files does not mean their content is already posted.

# Lean 4.19 to 4.34 compatibility port

The recovered source is preserved at commit 9074d0cebd4e132a6c1fa71c0817693246935398. The original archive checksums all matched before editing. The complete proof-source patch is LEAN4_34_PORT.patch.

Changes to the proof are limited to:

1. Remove six trailing `ring` calls where the updated `field_simp` already closes the goal.
2. Replace the removed `Finset.sort_sorted_lt` API with `Finset.sortedLT_sort.pairwise`.
3. Remove unused `Prod.fst` and `Prod.snd` simplifier arguments from the adjacent-divisor indexing proof.
4. Update the standalone header to identify the current environment.

The corresponding modular and standalone files receive the same changes. All mathematical definitions, construction formulas, theorem types, assumptions and proof strategy are preserved. The project now pins Lean 4.34.0 and Mathlib 5ed2965256430c3649e86755f9576b54eca72435, including all transitive dependency revisions in lake-manifest.json.

The current standalone proof and all seven axiom audits passed locally on Lean 4.34.0. The public workflow additionally checks both layouts, kernel replay, dependency revisions, a negative control and the pinned independent checker. Consult the workflow run for its actual outcome.

# Verification of the complete JSP-000506 submission

- Selected proof commit: `2aca2f16eba715d7ad672dfa017481b647c00063`.
- Branch: `jsp-000506-complete-kz` in `ketianzhang1-lang/jsp-000301-lean`.
- [Successful complete CI run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35395208909), run `35395208909`, job `105762358357`.
- Completed: `2026-09-18T21:35:58Z` (UTC).
- Lean: `leanprover/lean4:v4.31.0`.
- Mathlib: `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`; all nine package revisions checked.

| Check | Actual result |
| --- | --- |
| Original proof preservation | SHA-256 `3f469ec816a59782342009e1ad0df1d47a4b2d82e429c8f77f00a4d08210263e`; unchanged from `612b7cb093f17801ec6c6adf126c23619ad8fbd8` |
| Upstream source preservation | All six source/license/attribution inputs hash-verified; the complete proof's 480 embedded source modules remain unchanged |
| Strict compilation | Five units passed with `-DwarningAsError=true`: the complete upstream file, three local proof modules and one audit module |
| Axiom audits | 49 distinct targets: all 45 local public theorems and four credited upstream endpoints |
| Kernel replay | Erdos625SelfContained, JSP000506, JSP000506Bridge and JSP000506Complete all passed |
| Negative control | False arithmetic `1 = 0` rejected after importing the complete development |
| Independent checker | NaNoda checked 60,132 declarations with no errors, with hard rejection of unpermitted axioms |

The allowed axioms are exactly `propext`, `Classical.choice` and `Quot.sound`.
All 49 targets in `AUDIT_TARGETS.json` are also exported to NaNoda; their
closures contain no `sorryAx` or custom assumption replacing a proof.
The auditor checks that every local public theorem is included and that the
Lean audit and exporter lists agree. The strict source build checks every
declaration in the complete unchanged upstream file, including its embedded
release-root audit.

Leanchecker replays each selected module's declarations over its imports.
It uses Lean's own kernel and is not an independently implemented verifier.
NaNoda is a separate implementation and rechecks the transitive proof closures
exported for the 49 named targets. Its exporter is pinned to
`leanprover/lean4export` at `8554815c2dc6b7abe99ec1f08849c9759ba77947`;
NaNoda is pinned to `ammkrn/nanoda_lib` at
`4c544ed4099c8227f07d5de77ad1e69fb0740a27`.

The exported closure, strict checker configuration, printed target statements,
all build/replay logs and exact tested source archive are included in the
`jsp-000506-evidence` artifact, ID `10568293067`, with GitHub-reported
digest `sha256:7c54f1fa60d83f744ea7a6e470f195e5ca111e049427b696e9d0554841ecefc6`. SHA-256 records for the source archive and
checker export are included. Artifacts may expire; the pinned source,
upstream checksum manifest and reconstruction scripts remain reproducible.

The successful hosted run rebuilt the entire closure from a clean checkout
without local `--resume` reuse. A local run separately passed the same
five-unit build, 49 audits, four replay prefixes and negative control.
The NaNoda count above comes from the public run. Later documentation commits
record the receipt without changing the selected proof source.

The original endpoint `JSP000506.jsp_000506` has no finite-concentration
hypothesis. The exact probability-model and natural-subtraction equivalences
are proved in our bridge module. All natural orders, not only a subsequence,
are covered. The phase-dependent refinement outside the upstream Lean claim
is not included; see `STATEMENT_FIDELITY.md`.

This is contributor-run machine verification. It does not establish independent
human semantic review, peer review of the manuscript, first-formalization
priority, organizer acceptance or award eligibility. The earlier finite-only
receipt is preserved in `INITIAL_PARTIAL_VERIFICATION.md`.

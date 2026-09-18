# Verification of the complete JSP-000554 submission

- Selected proof commit: `21fcf006fd68b0bead9f979b704c92032f05cba8`.
- Branch: `jsp-000554-residue-reduction` in `ketianzhang1-lang/jsp-000301-lean`.
- [Successful complete CI run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35367960914), run `35367960914`, job `105674875217`.
- Date: 2026-09-18 (UTC).
- Lean: `leanprover/lean4:v4.34.0`.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`; all nine package revisions checked.

| Check | Actual result |
| --- | --- |
| Original proof preservation | SHA-256 `bb32c64b879462a8e70041a6b64d5a1e3a9022a2b8830668c119eff9430f9ff7`; unchanged from `2a6c737b5fb409a5600918cc5a2bab0a8dd174bb` |
| Source closure | All 51 upstream inputs and the three local modules compiled; no unpinned local imports |
| Strict compilation | All 54 modules passed with `-DwarningAsError=true` |
| Axiom audit | 37 distinct targets; only `propext`, `Classical.choice`, `Quot.sound` |
| Kernel replay | PrimeNumberTheoremAnd, UnitFractions, ErdosProblems, Util, JSP000554, JSP000554Complete all passed |
| Negative control | False arithmetic `1 = 0` rejected after importing the complete development |
| Finite diagnostic | Independently recomputed all six residue tables for gap lengths 2 through 12 |
| Independent checker | NaNoda checked 76,193 declarations with no errors; hard error on unpermitted axioms |

The 37 audited and exported targets are the original 23 public theorems,
12 integration theorems, and the two imported density endpoints. Their exact
names are in `AuditComplete.lean` and `scripts/verify_nanoda.sh`. No checked
closure depends on `sorryAx` or an added axiom filling a missing proof step.
The finite diagnostic is supplementary; the quantified claims are proved in Lean.

The exporter is pinned to `leanprover/lean4export` at
`6cea97789dc088ea47fcea15692db85685aedac5`; NaNoda is pinned to
`ammkrn/nanoda_lib` at `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.
The exported closure, strict checker configuration, printed target statements,
all build/replay logs and the tested source archive are included in the
`jsp-000554-evidence` artifact, ID `10557434804`,
with GitHub-reported digest `sha256:65c45bac5b02fd1d0a1b33312ceb58159e1670f3f17153e16bd3937065c7debe`.
The artifact contains separate SHA-256 records for the source and checker export.
GitHub artifacts may expire; the pinned source and scripts remain reproducible.

Earlier failed runs are retained as development history. They are not evidence
for the final result. Local incremental compilation was used to repair the port;
the successful hosted run above rebuilt the entire closure from a clean checkout.
Later documentation commits record these results without changing the tested proof.

This is contributor-run machine verification using an independent kernel
implementation in addition to Lean. It is not independent human certification,
organizer approval, an originality assessment or a guarantee of award eligibility.

# Verification of the complete JSP-000907 submission

- Selected proof commit: `555ce4f13bf7e8e8557020728f7f97ad3d1f51e0`.
- Branch: `jsp-000907-complete-kz` in `ketianzhang1-lang/jsp-000301-lean`.
- [Successful complete CI run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35389263216), run `35389263216`, job `105743535520`.
- Completed: `2026-09-18T20:12:37Z` (UTC).
- Lean: `leanprover/lean4:v4.34.0`.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`; all nine package revisions checked.

| Check | Actual result |
| --- | --- |
| Original note preservation | SHA-256 `584f4a2c9687de0b5484708ce2be7f71affadd588e247fee0d6deaec7b603a14`; unchanged from `bd9e587d1411903124531f14329d8df98b076692` |
| Pinned source closure | All 38 upstream inputs hash-verified, with exact recorded compatibility edits |
| Strict compilation | All 43 modules passed with `-DwarningAsError=true`: 38 upstream, four local proof modules, one audit module |
| Axiom audits | 35 distinct targets: 29 local public theorems and six credited upstream endpoints |
| Kernel replay | ErdosProblems, JSP000907Construction, JSP000907OddRim, JSP000907Witness and JSP000907Complete all passed |
| Negative control | False arithmetic `1 = 0` rejected after importing the complete development |
| Independent checker | NaNoda checked 19,125 declarations with no errors, with hard rejection of unpermitted axioms |

The allowed axioms are exactly `propext`, `Classical.choice` and `Quot.sound`.
All 35 audited targets in `AUDIT_TARGETS.json` are also exported to NaNoda;
their closures contain no `sorryAx` or custom assumption replacing a proof.
`AuditComplete.lean` records the matching Lean audit commands.

The exporter is pinned to `leanprover/lean4export` at
`6cea97789dc088ea47fcea15692db85685aedac5`; NaNoda is pinned to
`ammkrn/nanoda_lib` at `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.
The exported closure, strict checker configuration, printed target statements,
all build/replay logs and the tested source archive are included in the
`jsp-000907-evidence` artifact, ID `10565341477`, with GitHub-reported
digest `sha256:7d67fabd5fa6f936460319c8d3a2c28561798751eae7b8bf91308b71d6305768`. The archive includes SHA-256 records for
the tested source and checker export. Artifacts may expire; the pinned source
and reconstruction scripts remain reproducible.

The successful hosted run rebuilt the entire closure from a clean checkout
without local `--resume` reuse. A local full run independently passed the
same 43-module build, 35 axiom audits, five replay prefixes and negative
control. The NaNoda count above comes from the public run. Later documentation
commits record these results without changing the selected proof source.

The original two-question endpoint is `JSP000907.jsp_000907`. The full
negative answer uses the credited APSSV ten-chord family. Our own odd-rim
family's universal four-chord cap and criticality remain outside the formal
claim, as explained in `PROVENANCE.md` and `STATEMENT_FIDELITY.md`.

This is contributor-run machine verification using an independent kernel
implementation in addition to Lean. It does not establish independent human
semantic review, first-formalization priority, organizer acceptance or award
eligibility.

# JSP-000250 verification

**Result: passed on 2026-09-18.** This record applies to the complete integrated
proof at `e2f4c737ad4c2c9d7f4dcbfd4214fd2f2c96c876`, on branch
`jsp-000250-prime-obstruction` of `ketianzhang1-lang/jsp-000301-lean`.
Documentation-only descendants do not replace that tested proof version.

- [Complete hosted run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35362198703).
- [Verification job](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35362198703/job/105655920803).
- [Machine-readable receipt](HOSTED_VERIFICATION.json).

| Check | Observed result |
| --- | --- |
| Immutable upstream inputs | 75 original and ported source hashes verified |
| Pinned dependencies | All nine revisions matched the lockfile |
| Complete compilation | All 78 modules passed, warnings treated as errors, without resume |
| Axiom closures | All 21 targets passed; only `propext`, `Classical.choice`, `Quot.sound` |
| Kernel replay | All five proof-module prefixes passed |
| Negative control | The false arithmetic statement `1 = 0` was rejected |
| Independent NaNoda | **Checked 75850 declarations with no errors** |
| Source/log archival | Successful; artifact `jsp-000250-evidence`, ID `10555054549` |

The five replay prefixes are `PrimeNumberTheoremAnd`, `UnitFractions`,
`ErdosProblems`, `JSP000250` and `JSP000250Complete`. The audited and exported
target list includes all eleven original upper-proof theorems and all ten
integration theorems, including `JSP000250.jsp_000250` and
`JSP000250.liu_sawhney_resolution`.

Lean is pinned to 4.34.0 and Mathlib to
`5ed2965256430c3649e86755f9576b54eca72435`. The independent-checker script pins
lean4export to `6cea97789dc088ea47fcea15692db85685aedac5` and NaNoda to
`4c544ed4099c8227f07d5de77ad1e69fb0740a27`. Its permitted-axiom set is exactly
the three axioms listed above, with unpermitted axioms causing a hard error.
The checked theorem closures do not depend on `sorryAx` or replacement axioms.

The workflow artifact contains the tested source archive and commit identity,
locked dependencies, source hashes, build and replay logs, 21 axiom reports,
the negative-control log, checker configuration and logs, printed target
statements, and the compressed exported proof closure. Artifact SHA-256:

`7382e956c4cb66ade49cfb7672ed2b7dd41e46ace15c4751fc7cdaf7c2042502`

GitHub reports artifact expiry on 2026-12-17; the immutable source and checking
scripts remain the basis for reproduction after artifact retention ends.

These are contributor-run checks. NaNoda is an independent checker
implementation, not an independent human reviewer. Kernel acceptance does
not by itself establish intended-statement fidelity, authorship, priority,
contribution eligibility or organizer approval. The statement correspondence
and provenance are supplied separately for maintainer review. Earlier
upper-only verification and unsuccessful compatibility-port iterations are
not the proof version selected here.

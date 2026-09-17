# Verification record — 2026-09-17

The exact source in this package passed the following local checks.

| Check | Exit | Seconds |
| --- | ---: | ---: |
| Main source elaboration, kernel checking and object export | 0 | 22.225 |
| Audit source elaboration and object export | 0 | 11.886 |
| Explicit `leanchecker --verbose JSP000443` replay | 0 | 10.214 |
| False theorem `1 = 0` negative control | 1, correctly rejected | 9.408 |

The nine axiom reports in `verification/local-Audit.log` each use a subset
of `propext`, `Classical.choice`, and `Quot.sound`. In particular the exact
Ramsey-value theorem and both standard graph-copy bridges contain no
`sorryAx`, custom axiom or compiler-trust axiom. The finite checks use
`decide +kernel`, not native evaluation as a proof oracle.

The independent Python reconstruction agrees with all 20 Lean bitmasks:
20 vertices, 46 edges, minimum degree 4, at most one common neighbor for
distinct vertices. This diagnostic is not needed to trust the Lean proof.

Source SHA-256:
`e9af3522e33a292c1f53a54414a9aa92e01e7f92a7ca24c44d6395e0069b092a`.
`verification/manifest.json` records exact source, wrapper and log hashes.
Process receipts retain the actual executed commands and elapsed times.

## Environment and boundaries

Lean 4.34.0 and the shared compiled Mathlib cache identified by the pinned
lockfile were used. Main/Audit compilation used the supplied
`scripts/local_frontend/lakefile.lean` wrapper, calling
`Lean.Elab.runFrontend` with trust level **0** and exporting the corresponding
object files. The regular `lean` launcher could not locate its application
in this container. The wrapper does not add proof axioms or bypass the kernel.

The bundled `leanchecker` subsequently replayed the main module itself; its
log says `replaying JSP000443`. It uses the same Lean kernel implementation,
so this is not a second independently implemented checker. Imported Lean
and Mathlib artifacts were not rebuilt or replayed in full.

No GitHub Actions run, `lake build --wfail` result, NaNoda result or
independent human review is claimed. The standard workflow and NaNoda
reproduction scripts are prepared but have not been executed. Public
publication is pending user approval after automatic review blocked the
push. Organizer review, scope/priority assessment and award eligibility
remain pending.

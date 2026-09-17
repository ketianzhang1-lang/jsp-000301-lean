# Verification status

Exact source hashes and actual local logs accompany this package. Public CI information will be added only after observing its result.

Environment: Lean 4.34.0, compiler commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b; Mathlib target revision 5ed2965256430c3649e86755f9576b54eca72435. All nine transitive package revisions are fixed in lake-manifest.json. Local checking reuses an existing Mathlib cache; its source revision cannot be independently established from local Git metadata. Public reproduction checks the actual revisions against the manifest.

The local Linux environment requires a process-executable-path compatibility shim redirecting only the process's own /proc/<pid>/exe lookup to /proc/self/exe. It changes no Lean source or proof-checking rules. Public CI runs without this shim.

Compilation and the bundled Lean checker share implementation. NaNoda is a separate checker implementation. Contributor-run checks are not independent human review or organizer certification. Statement fidelity, priority, eligibility, recipient confirmation, and award decisions remain for the organizers. CI artifacts have finite retention; source and compact logs are committed separately.

## Observed local results

Compilation with warnings treated as errors, bundled kernel replay, all nine target axiom audits, and rejection of the false arithmetic control passed. The nine axiom closures use only `propext`, `Classical.choice`, and `Quot.sound`. NaNoda has not yet been run for this package.

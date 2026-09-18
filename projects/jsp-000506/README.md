# JSP-000506: complete-statement integration in preparation

This branch retains our original finite concentration proof and develops the
bridges to the complete original Erdős 625 asymptotic statement. Verification
of the integrated package is in progress; this preparation commit does not
claim a successful complete build.

The unchanged upstream source is by **Samuil Petkov**, *Erdős Problem 625:
Manuscript and Lean Formalization*, https://github.com/SamPetkov/Erdos,
licensed under **CC BY 4.0**. We pin source commit
`b3fdc4d3efbe6c999faac3da4614cc3036b3b3ea` and preserve the original source bytes,
license, license-scope document and citation. `UPSTREAM.json` records the URL
and both Git and SHA-256 hashes. No changes are made to the upstream proof.
The single upstream file contains its complete 480-module source closure.

Our `JSP000506.lean` is unchanged from the preceding branch. Our new
`JSP000506Bridge.lean` and `JSP000506Complete.lean` connect graph encodings,
colouring invariants, exact counting probabilities and fixed-threshold limits.
Our local files use Apache 2.0; that license does not relicense Petkov's work.
The original finite result's mathematics is due to Annika Heckel.

Lean and Mathlib are fixed to 4.31.0 to preserve the complete proof unchanged.
`python3 scripts/bootstrap.py` reconstructs all exact upstream files.
The preparation workflow builds the pinned dependencies and checks the
unchanged upstream and original finite proof. The original historical
partial-scope documentation remains in files prefixed `INITIAL_PARTIAL_`.

We claim our finite formalization, model bridges and integration work, not
ownership or first-formalization priority for the imported complete proof.

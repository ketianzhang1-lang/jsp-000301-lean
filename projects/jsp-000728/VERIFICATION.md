# Executed verification of JSP-000728

The contributor-run checks completed successfully on **2026-09-18 UTC**.
We verified the complete original relative-count endpoint, including its fixed
exponential separation and the independent all-interval lower construction.

## Checks actually passed locally

- **47 modules** compiled with warnings as errors: 43 upstream modules, our
  three proof modules and the complete audit module.
- **27 theorem-closure axiom reports** passed the exact allowlist `propext`,
  `Classical.choice`, `Quot.sound`. This includes every public theorem in our
  three modules, both full imported endpoints and the strict exponent bound.
  No `sorryAx`, compiler-trust or added custom axiom is present in those closures.
- Lean kernel replay of all **43 upstream modules** under `ErdosProblems`,
  plus `JSP000728`, `JSP000728Bridge` and `JSP000728Complete`.
- All **nine actual dependency Git revisions** match the committed manifest.
- All **43 original Git blob hashes and source SHA-256 hashes**, the exact
  recorded transformations and the resulting source SHA-256 hashes agree.
  Eight upstream files have explicitly marked compatibility changes.
- A false-arithmetic control importing the complete project was rejected with
  the expected proof-failure diagnostic.
- Our original lower-bound module is byte-identical to proof revision
  `91fdee92a0e9122b9e41cfd3b24d0ab70a64b3c0`; its toolchain and dependency
  manifest are unchanged.

[verification/verification.json](verification/verification.json) gives every
compiled module and its source/object hashes. The successful local build
resumed interrupted work using exact source-hash matches and existing successful
build logs; changed source and dependent modules had first been recompiled in
dependency order. The audit, all kernel replays and negative control were then
freshly executed. The public verifier compiles every module by default.

[verification/axioms.log](verification/axioms.log), the adjacent kernel logs,
[negative control](verification/negative-control.log), and
[verification/local-verification.log](verification/local-verification.log)
record the executed results. [SOURCE_SHA256SUMS](verification/SOURCE_SHA256SUMS)
fixes the published local inputs; `UPSTREAM.json` fixes imported source bytes.

## Reproduction and independent-checker boundary

Use Lean **4.34.0**, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, the committed manifest and the
commands in [README.md](README.md). `scripts/bootstrap.py` downloads only pinned
source and performs the recorded compatibility changes. No upstream compiled
objects are downloaded. Pinned cached Mathlib objects are used.

The local preparation checkout was
`91fdee92a0e9122b9e41cfd3b24d0ab70a64b3c0`, with the new bridge, endpoint,
source manifest and scripts identified by the hashes in this receipt. The
publishing commit adds these exact verified files and their documentation.
The preparation SHA alone does not contain the newly completed proof.

Leanchecker uses Lean's own kernel; it is not a separately implemented checker.
NaNoda was not run locally because this environment lacked Rust/Cargo. The
[public workflow](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/workflows/jsp-000728.yml)
builds the pinned Lean exporter and NaNoda checker, exports all 27 target theorem
closures and uses the same strict axiom allowlist. Only a successful run with
`head_sha` equal to the selected public proof commit establishes that hosted
check; consult the actual run rather than inferring success from this workflow.

These are reproducible contributor-run checks, not independent human review,
organizer acceptance, first-formalization priority or award certification.

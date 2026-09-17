# Verification

## Local checks completed

All six proof modules compiled with Lean 4.34.0, with warnings promoted to
errors. All nine target axiom audits passed, listing only `propext`,
`Classical.choice`, and `Quot.sound`. The final endpoint is
`CatlinComplete.catlin_counterexample`. The local transcripts are preserved
in `evidence/local-build.log` and `evidence/local-axioms.log`.

No unfinished proof placeholders, custom axioms or `native_decide` are used.
The finite profile check uses ordinary kernel reduction. Source-level checks
and compiler acceptance are separate from semantic review of the statements.

The local environment used existing cached dependencies and a process-path
compatibility shim needed to launch the compiler in this environment. The
shim redirects executable-path lookup to `/proc/self/exe`; it does not modify
the proof checker. The local Mathlib cache does not retain a usable Git HEAD,
so exact dependency revisions are not inferred from that cache. The cloud
workflow checks actual dependency Git revisions against the committed manifest.

## Reproduction and cloud verification

With the pinned toolchain installed, run from this directory:

    lake exe cache get
    bash scripts/verify.sh
    bash scripts/verify_nanoda.sh

The manifest pins Mathlib to `5ed2965256430c3649e86755f9576b54eca72435`.
The workflow uses pinned action revisions. The first script builds, replays
all six modules with bundled `leanchecker`, audits nine roots, checks every
dependency revision, and requires rejection of a false-arithmetic control.
The second exports the nine roots and checks their transitive closures using
pinned lean4export and NaNoda revisions, with a strict axiom allowlist.

A cloud result is not yet asserted in this revision. A later receipt will
record the actual tested commit, run, checker result and artifact metadata.
Artifacts have finite retention. Contributor-run checks are not independent
human review or organizer certification, even when the checker implementation
is independent of Lean.

# Copy-ready metadata for PR #443

Use the copy button on each code block to replace the title and body of the existing [PR #443](https://github.com/TheJustinSunPrize/awards/pull/443).

## Title

```text
JSP-000140: complete colouring asymptotic with our strict finite lower bound
```

## Body

````markdown
## Complete statement

We submit the complete asymptotic answer to JSP-000140 / Erdős 136:

**f(n,4,5) = (5/6)n + o(n)**,

where every four vertices of a complete graph must span at least five distinct edge colours. This replaces the earlier lower-bound-only scope of this PR.

Our endpoint `JSP000140.jsp_000140` combines:

- The strict finite lower estimate `5*(n-1)/6 + 1 <= minPalette n` for every `n >= 4`, using natural-number division.
- The normalized limit `minPalette n / n -> 5/6`.
- For every positive `epsilon`, actual admissible colourings for all sufficiently large `n` using fewer than `(5/6 + epsilon)*n` colours.

## Our contribution and attribution

We retain our original 22-theorem lower-bound development unchanged, including fork packing, colour-incidence estimates, the strictness argument and the four-vertex-set formulation. We add 22 theorems for the exact pair/edge-colouring correspondence, attained minima, strict lower bounds in the standard model, and the full asymptotic endpoint. Equality of the two minimum palette sizes is proved for `n >= 2`; the diagonal-value boundary for smaller sizes is explicit.

We prepared this work under GitHub account `ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance. We also provide the pinned source closure, compatibility port, statement correspondence and reproducible verification.

The lower-bound mathematics is classical. The complete asymptotic answer is due to Bennett, Cushman, Dudek and Prałat; the reused construction also uses the Joos–Mubayi matching approach. We reuse the [complete development in plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos136.lean), whose entry credits Codex and GPT-5.6 Sol. Its 20-module transitive closure, source hashes, compatibility edits, author notices and licenses are retained or recorded.

We transport the existing full asymptotic theorem through our exact model bridge; the imported closure also includes its classical lower argument. Our original strict finite lower theorem is retained as an additional conclusion. We do not claim the imported proof as our original work or first-formalization priority.

## Pinned proof and reproduction

- Repository: `ketianzhang1-lang/jsp-000301-lean`
- Branch: `jsp-000140-coloring-kz`
- Full tested proof commit: `724a733a2b498d7b3b956e66b76d7334cc906eaf`
- Main theorem: [`JSP000140.jsp_000140`](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/724a733a2b498d7b3b956e66b76d7334cc906eaf/projects/jsp-000140/JSP000140Complete.lean)
- [README and build instructions](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/728526da93d79904fec57572a84e1202b5a8a93d/projects/jsp-000140/README.md)
- [Statement fidelity](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/728526da93d79904fec57572a84e1202b5a8a93d/projects/jsp-000140/STATEMENT_FIDELITY.md)
- [Contribution and provenance](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/728526da93d79904fec57572a84e1202b5a8a93d/projects/jsp-000140/PROVENANCE.md)
- [Verification record](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/728526da93d79904fec57572a84e1202b5a8a93d/projects/jsp-000140/VERIFICATION.md)

```sh
git clone --branch jsp-000140-coloring-kz https://github.com/ketianzhang1-lang/jsp-000301-lean.git
cd jsp-000301-lean
git checkout 724a733a2b498d7b3b956e66b76d7334cc906eaf
cd projects/jsp-000140
elan toolchain install "$(cat lean-toolchain)"
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

Lean is pinned to 4.34.0; Mathlib and all nine dependency revisions are locked. The NaNoda script additionally requires Rust.

The [complete hosted verification run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35347120839) passed on 2026-09-18: all 24 proof/audit modules compiled with warnings treated as errors; all 46 axiom audits, the proof-module kernel replays and the negative control passed. Independent NaNoda checked **56,007 declarations with no errors**, using a hard-error allowlist containing only `propext`, `Classical.choice` and `Quot.sound`. The checked proof closures do not rely on `sorryAx` or replacement axioms.

This PR changes only the JSP-000140 catalog entry. We request review of the complete statement and our disclosed contribution. Machine verification does not establish award eligibility, priority or organizer approval.

````

# JSP-000140: complete colouring asymptotic with our strict lower bound

We formalize the minimum number of colours needed so that every four vertices
of a complete graph see at least five edge colours. Our original 22-theorem
lower-bound development is retained unchanged. We add an exact bridge to the
standard unordered-edge definition, an attained minimum in our original model,
and the complete asymptotic conclusion using an attributed upper construction.

The endpoint is **`JSP000140.jsp_000140`** in
[JSP000140Complete.lean](JSP000140Complete.lean). It combines:

- Our strict finite lower estimate, including its integer form
  `5*(n-1)/6 + 1 <= minPalette n` for every n >= 4.
- The full limit `minPalette n / n -> 5/6`.
- For every epsilon > 0, actual admissible colourings for all sufficiently large
  n using fewer than `(5/6 + epsilon)*n` colours.

[JSP000140Bridge.lean](JSP000140Bridge.lean) proves both directions of the
colouring correspondence and equality of minimum palette sizes for n >= 2.
Diagonal pair values are ignored by admissibility; they cannot be silently
counted as genuine edges. The minimum comparison explicitly handles that boundary.
[JSP000140Complete.lean](JSP000140Complete.lean) also proves asymptotic equivalence
and transfers our strict lower bound to the standard edge-colouring function.

## Our contribution and reuse

We prepared this formalization under GitHub account `ketianzhang1-lang`, with
OpenAI ChatGPT/Codex assistance. Our original lower proof contains the fork
packing, colour-incidence estimates, strictness argument and vertex-subset
formulation. Our two new modules add 22 public theorems for the model bridge,
minimum-palette statements and full endpoint.

The complete upper construction is reused from
[plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos136.lean).
Its exact 20-module transitive source closure is pinned in
[UPSTREAM.json](UPSTREAM.json). Source is fetched and compiled, rather than
substituting an assumed matching theorem or copying prebuilt proof objects.
[PROVENANCE.md](PROVENANCE.md) records authorship, mathematical credits, porting
changes and the distinction between our work and the reused general proof.

## Reproduce

Repository: `ketianzhang1-lang/jsp-000301-lean`; branch: `jsp-000140-coloring-kz`.
Check out the full proof commit recorded in the catalog, then run:

```sh
cd projects/jsp-000140
elan toolchain install "$(cat lean-toolchain)"
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

Lean 4.34.0 and all nine dependency revisions are pinned. Mathlib is fixed to
`5ed2965256430c3649e86755f9576b54eca72435`. The NaNoda script also requires Rust.
The pipeline compiles 24 modules, audits 46 theorem closures, replays the proof
modules and requires rejection of an invalid arithmetic statement. NaNoda
checks the complete exported dependency closures with a strict three-axiom
allowlist. [VERIFICATION.md](VERIFICATION.md) distinguishes executed results
from a verification recipe.

The original statement and quantifiers are documented in
[STATEMENT_FIDELITY.md](STATEMENT_FIDELITY.md). This package updates
[PR #443](https://github.com/TheJustinSunPrize/awards/pull/443). Maintainers
must assess the contribution and complete statement; automated checks do not
establish award eligibility or priority.

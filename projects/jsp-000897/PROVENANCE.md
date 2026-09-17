# Provenance and contribution scope

This is an attributed port and supplement to an existing complete Lean proof, not a first formalization or a new mathematical solution.

## Upstream source

- Repository: https://github.com/plby/lean-proofs
- Immutable commit: `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
- File: `src/latest/ErdosProblems/Erdos1079.lean`.
- URL: https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1079.lean
- The byte-identical original is retained in `upstream/Erdos1079.lean`.
- Original SHA-256: `09efec8509c86a61575eed184fd68d76d09a4f74ca94b7338478cb5657f9cae3`.
- The source explicitly supplies an Apache-2.0 notice and credits Codex and GPT-5.6 Sol for formalization. That notice and the prior credits are retained. Its standalone instructions target Lean/Mathlib 4.33.0.

## Changes in this package

`Erdos1079.lean` ports the existing proof to Lean/Mathlib 4.34.0: deprecated theorem names are updated, the bipartite Turan-number induction explicitly changes its target to `turanNumber`, and redundant tactic imports are removed. The original theorem statements are retained.

`JSP000897.lean` adds the explicit integral-surplus theorem at every maximum-degree vertex, a full existence endpoint retaining the exact surplus, the equivalent surplus-difference comparison, and the strict version. These are consequences of the credited existing argument. No mathematical novelty or global formalization priority is claimed.

The package also supplies a pinned build, typed axiom audits, negative control, Lean kernel replay, and NaNoda export/check scripts. Verification results are reported separately in VERIFICATION.md.

## Mathematical credit

Bela Bollobas and Andrew Thomason, *Dense neighbourhoods and Turan's theorem*, Journal of Combinatorial Theory, Series B 31 (1981), 111-114, DOI https://doi.org/10.1016/S0095-8956(81)80016-0.

J. A. Bondy, *Large dense neighbourhoods and Turan's theorem*, Journal of Combinatorial Theory, Series B 34 (1983), 109-111. The strict threshold version is credited to Bondy by the upstream proof. Mathlib provides Turan's extremal theorem and the finite-graph infrastructure.

The submitting account is responsible only for the port, supplement and reproduction package, prepared with OpenAI ChatGPT assistance. The submission does not act on behalf of the mathematical authors or upstream formalizers. Original credits must not be reassigned to the submitting account.

# Sources and contribution

1. Walter E. Mientka and Roger C. Weitzenkamp, *On f-plentiful numbers*,
   Journal of Combinatorial Theory 7 (1969), 374–377,
   [DOI](https://doi.org/10.1016/S0021-9800(69)80067-0).
   The finite-range result is attributed to them by Formal Conjectures.
2. [Formal Conjectures, Erdős 1142](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1142.lean),
   copyright 2026 The Formal Conjectures Authors, Apache-2.0. The precise
   predicate and target statement are reproduced/adapted here. The proof,
   sieve, finite certificates, bridges, and verification scripts were written
   for this contribution; upstream placeholder proofs are not imported.
3. [OEIS A039669](https://oeis.org/A039669) lists the seven examples and
   reports a later computational bound of 2^120 (Max Alekseyev, December 8,
   2011). This contribution does not improve that bound and makes no new
   mathematical-result claim. The OEIS text or program is not copied.
4. Lean and mathlib provide the proof infrastructure; exact versions appear
   in the toolchain and dependency lock. Prior verification scaffolding in
   the contributor's repository is adapted, retaining its pinned checkers.

The submitted contribution is a complete machine-checked proof of the
specified classical finite-range variant, an untrusted-table verifier with
proved coverage, and reproducible verification infrastructure. Prepared for
Ketian Zhang with OpenAI ChatGPT / Codex assistance. This description does
not assert global formalization priority or prize entitlement.

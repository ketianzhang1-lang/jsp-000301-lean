# Contribution and source provenance

We prepared the original `JSP000554.lean` under GitHub account
`ketianzhang1-lang`, with OpenAI ChatGPT assistance. Its 23 public theorems
prove the exact residue criterion for every gap length at least two, the
finite counting identity and the complete tables for lengths 2, 4, 6, 8, 10
and 12. The file remains byte-identical to commit
`2a6c737b5fb409a5600918cc5a2bab0a8dd174bb`; `ORIGINAL_PROOF_SHA256` records its hash.
It imports Mathlib and no external problem proof.

We add 12 public theorems in `JSP000554Complete.lean`. They identify our
endpoint-based predicate with the consecutive-prime-index predicate, retain
the first gap from 2 to 3, transport the complete density-one and density-zero
conclusions to our definitions, express both as limits of actual counts, and
connect the complete conclusion to our uniform residue classification.
We also prepare the pinned source closure, compatibility port and verification.

The mathematics is attributed to Ayla Gafni and Terence Tao,
[Rough numbers between consecutive primes](https://arxiv.org/abs/2508.06463),
Theorem 1.1 and Section 4, with the earlier authors cited there.
Our exact tables are computed from their residue definition and proved in Lean.
We make no new mathematical-discovery claim.

The complete analytic proof is reused from
[plby/lean-proofs at 8822f7d](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest).
The Erdős 682 entry credits Codex and GPT-5.6 Sol as formal authors.
Its transitive closure contains 51 source modules, including sieve theory,
the prime number theorem, natural-density utilities and their dependencies.
We preserve their original source headers and add explicit modification notices
to the compatibility-ported files. The Formal Conjectures authors,
the PrimeNumberTheoremAnd contributors, UnitFractions contributors, Mathlib
authors and other named upstream authors retain their respective credits.
The complete density proof is an imported dependency, not our original proof.

`UPSTREAM.json` records original URLs, Git blob hashes, SHA-256 hashes,
all compatibility changes and the hashes of the resulting source files.
`scripts/bootstrap.py` verifies these hashes before using the imported source.
`UPSTREAM-LICENSE` preserves the distributor's license notice. The accompanying
[APACHE-2.0.txt](APACHE-2.0.txt) supplies the Apache 2.0 license for the source files
that carry that license. The repository-root MIT license does not replace any
third-party or per-file Apache license. Original copyright, author and modification
notices remain in the source. Exporter and NaNoda authors retain their licenses.

This documentation correction adds the previously missing local Apache license
copy and fixes the earlier inaccurate reference to a project `LICENSE` file.
It does not alter the selected proof commit
`21fcf006fd68b0bead9f979b704c92032f05cba8`, proof statements, dependency revisions,
or verification scripts.

We request assessment of our independently prepared finite classification,
statement correspondence, integration and verification. No global first
formalization priority, organizer acceptance or award entitlement is asserted.

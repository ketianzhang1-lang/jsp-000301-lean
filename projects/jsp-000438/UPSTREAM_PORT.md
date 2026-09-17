# Credited dependency and mechanical port

The mathematical Erdős–Sós proof is **not a new contribution of this project**.
It is reproduced under Apache-2.0 from:

- Repository: https://github.com/tadamcz/erdos548
- Commit: `82ffb751f3d37768927df9239ed08439bbe0dd09`
- File: `Erdos548/Resolutions/Erdos548_192usd_21h.lean`
- Copyright and benchmark attribution: see `NOTICE` and `upstream-original/README.md`.
- Upstream credits GPT-6 Astra (OpenAI), the FrontierMath Erdős benchmark,
  Tom Adamczewski / Epoch AI, and Thomas F. Bloom.

`upstream-original/Erdos548_192usd_21h.lean` is an unmodified reference copy.
`Upstream548.lean` is the compiled port to Lean / Mathlib 4.34.0.
`UPSTREAM_PORT.patch` records every difference. Changes are:

1. Replace the aggregate Mathlib import with the required focused imports.
2. Normalize a natural-number cast in the factorial identity.
3. Wrap the graph symmetry proof in the new `Std.Symm` constructor.
4. Use the current `isBridge_iff` conclusion directly (remove the old projection).
5. Update deprecated tactic and theorem names, replace proposition-valued
   `haveI` with `have`, and remove one unused simplifier argument.
6. Add the attribution / modification notice at the top of the port.

No mathematical hypothesis, conclusion, counting argument, or induction is
replaced by an assumption. The downstream axiom audit checks the actual
`Erdos548.tree_free_edge_bound` dependency as well as all main consequences.

SHA-256 of exact upstream source: `7e5f0d9a5573eef054dee6831edf7e785ea689f03f53cb800b896b12d3277fa1`.

SHA-256 of compiled port: `460409e526f8a52c96fa0163073c9b6d9cbeb36722823a800cb172457e4b6602`.

The two Ramsey definitions in `RamseyDefinitions.lean` are copied verbatim from
`google-deepmind/formal-conjectures` commit
`40e7c98697de6f66b8cbdbf641749ab39ed9c152`, file
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean`.
Copyright 2026 The Formal Conjectures Authors, Apache-2.0.
The imported statement is the universal theorem in
`FormalConjectures/ErdosProblems/547.lean` at the same commit; research-category
metadata is omitted from the standalone project.

The existing `plby/lean-proofs` treatment of Erdős 547 (commit
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`) was consulted during scope review.
It explains the conditional reduction and supplies the sufficiently-large
case. This project supplies the all-order dependency and a new standalone
Lean 4.34 integration, not a claim to discovering the mathematical implication.

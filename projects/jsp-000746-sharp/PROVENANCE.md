# Source attribution and contribution

We identify GitHub account `ketianzhang1-lang` as the contributor for the explicit 43-edge witness, its Lean checks, restriction to all smaller orders, exact-threshold integration, the integer-graph transport and endpoint, and this reproduction project. We developed these additions with OpenAI ChatGPT assistance.

The mathematical upper bound is credited to Ben Barber in the original source and the official catalog. The reused upper-bound Lean proof credits Codex and GPT-5.6 Sol:

- Repository: https://github.com/plby/lean-proofs
- Commit: `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`
- Main source: `src/latest/ErdosProblems/Erdos895.lean`
- Certificates: `src/latest/ErdosProblems/Erdos895/Certificate.cnf` and `Certificate.lrat`.

[UPSTREAM.json](UPSTREAM.json) records the immutable URLs and SHA-256 hashes. Bootstrap fetches those bytes and preserves the attribution header. For Lean 4.34, it replaces the broad `import Mathlib` with `Mathlib.Combinatorics.SimpleGraph.Clique` and `Mathlib.Tactic`; the SAT import, theorem statements, proof bodies and certificates are unchanged. The resulting port hash is also checked.

The new source does not claim the upstream proof or the mathematical upper bound as our invention. The parent repository's license for our additions does not relicense upstream material. Lean, Mathlib and the referenced upstream sources retain their own attribution and licensing.

The earlier finite supplement was verified at `b62eb3c313e08907fc76fe927cf28545a38178e0` under Lean 4.33. Its old run does not certify the newly added integer endpoint or the Lean 4.34 project. The current verification receipt identifies the new execution separately.

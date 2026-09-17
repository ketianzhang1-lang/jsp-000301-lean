# Contribution and dependency attribution

We identify GitHub account `ketianzhang1-lang` as the contributor for the explicit restriction encoding, orientation-preservation proof, all-orders transport, fifteen-vertex endpoint, extremal-function disproof integration, the Lean local exclusion certificates and the verification package. We developed this work with OpenAI ChatGPT assistance.

## Complete main proof dependency

The main theorem uses the fourteen-vertex theorem of K. B. Reid and E. T. Parker, *Disproof of a conjecture of Erdős and Moser on tournaments*, Journal of Combinatorial Theory (1970), 225–238, as formalized in:

- Repository: https://github.com/plby/lean-proofs
- Commit: `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`
- Files: `src/latest/ErdosProblems/Erdos1216.lean` and `src/latest/ErdosProblems/Erdos1216/Certificates.lean`.
- Formalization credit retained from their headers: Codex / GPT-5.6 Sol; the files retain their Apache-2.0 notices.

[UPSTREAM.json](UPSTREAM.json) pins both original SHA-256 hashes. Bootstrap retrieves the files for compilation, with their headers retained. For Lean 4.34, the main module replaces the deprecated simp-lemma names `if_false` and `if_true` with `ite_false` and `ite_true`; the theorem statements, proof structure and certificate module are unchanged. The ported file hash is checked separately. They are not copied into the prize repository or attributed to our account. Our MIT-licensed additions do not relicense the imported source.

## Our independent reproduction and local certificates

The earlier `reproduction/PROOF.md` and Python checker reconstruct the fifteen-vertex argument. Our `FiniteChecks.lean` verifies the local two-vertex exclusions and final forced-model witness using explicit finite certificates. Its witness search is untrusted: the resulting concrete witnesses are checked by Lean.

The main Lean theorem uses the credited fourteen-vertex proof followed by our transport lemmas. It does not assert that the entire independent fifteen-vertex reconstruction has been formalized, and it does not treat Python output as a proof axiom. The full Lean conclusion nevertheless resolves the proposed universal equality negatively.

These contributions are submitted for formalization review. Repository ownership, successful compilation and mathematical sufficiency alone do not establish first-formalization priority or award eligibility.

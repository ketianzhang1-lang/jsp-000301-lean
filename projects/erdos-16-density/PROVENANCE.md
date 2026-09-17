# Sources and attribution

## Mathematical result

Yong-Gao Chen, *A conjecture of Erdős on p + 2^k*, [arXiv:2312.04120v2](https://arxiv.org/html/2312.04120v2), 10 December 2023. This is the inspected version for the one-progression theorem. Chen receives mathematical credit. No claim concerning stronger later versions is made.

## Existing Lean prerequisite

[Pinned Erdos16.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos16.lean).

- Commit: `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
- SHA-256: `939a0a7178f416b3e3a6606ff56f637e1dc5f91f29e75a8e54f6456c44a4d475`.
- Its header names Yong-Gao Chen as informal author and Gemini 3.1 Pro, Antigravity, and Daniel Chin as formal authors.
- It points to [Daniel Chin's proof repository](https://github.com/danielchin/proofs/blob/main/Proofs/ErdosProblems/Erdos16.lean). That moving URL is attribution context; it is not the build dependency.
- The unchanged prerequisite is fetched and hash-checked, not redistributed. No additional license permission is inferred from public availability.
- The source labels `density_zero` as absence of an infinite arithmetic progression. This is explicitly distinguished from the real-valued density limit in the supplement.

## Reference statement

[Google DeepMind Formal Conjectures, Erdős 16](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/16.lean). This records the standard counting-limit statement with nonnegative exponents and credits Chin using Aristotle. That reported tool attribution differs from the prerequisite's header; neither is silently replaced. The reference repository supplies a statement with an unproved proof placeholder; it is not imported as proof evidence here.

## New contribution

`Erdos16Density.lean` and `Alignment.lean` were prepared with OpenAI ChatGPT/Codex assistance for the submitting account. The contributor claims only the new bridge and boundary formalization, not the original mathematical result, first global formalization, or other authors' work. Any recipient identity and allocation require organizer confirmation; proposed placeholder `RECIPIENT-ERDOS16-KZ-A` is unconfirmed.

## Dependencies and trust

Lean 4.34.0; Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435` and transitive revisions in `lake-manifest.json`. The exporter and NaNoda revisions are pinned in `scripts/verify_nanoda.sh`. Cached Mathlib artifacts are used; a complete rebuild of Mathlib from source is not claimed. Axiom audits and replay are separate from statement review and award assessment.

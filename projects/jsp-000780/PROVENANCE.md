# Provenance and contribution

The binomial construction for every r≥6 is attributed to GPT-5.5 Pro prompted
by Liam Price in the [pinned Formal Conjectures source](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/939.lean).
That source links to the [original discussion](https://www.erdosproblems.com/forum/thread/939).
The discussion returned HTTP 403 in this session; attribution and the described
construction were checked against the immutable public statement source.

This independently written Lean implementation specializes the construction to
r=6, uses a=30(t+11)+1 instead of a variable prime, proves distinctness,
collective gcd 1 and infinitude, and bridges the exact source predicates.
It is not new mathematics. OpenAI ChatGPT assistance is disclosed; the
submitting account directed this work. Mathematical credit remains with the
contributors above and with the historical authors for their separate results.

The source `Nat.Full` definition is recorded at
[Full.lean](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjecturesForMathlib/Data/Nat/Full.lean),
and collective coprimality at
[Prime/Finset.lean](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjecturesForMathlib/Data/Nat/Prime/Finset.lean).
No third-party proof code is copied into the development. Standard Mathlib
infrastructure is used under its existing license. The verification scripts
adapt scripts already in the submitting account's proof repository.

A search of the official repository's issues and PRs for JSP-000780 and
Erdős/Erdos 939 returned no matches on 2026-09-17. This bounded search does not
establish global priority or absence of other formalizations. The catalog at
f4e7173d89dfe91022a185427d63452c8ffbf6ae records progress and no Lean proof.

# Problem and original source

Erdős Problem 16: can the odd integers not representable as a prime plus a power of two be written as one infinite arithmetic progression together with a set of natural density zero?

Original question: https://www.erdosproblems.com/16

Inspected proof of the one-progression result: Yong-Gao Chen, *A conjecture of Erdős on p + 2^k*, https://arxiv.org/html/2312.04120v2

I did not locate a matching record in the 1,022-item prize catalog at `f4e7173d89dfe91022a185427d63452c8ffbf6ae`. Please identify an existing record if this search missed one, or assess this problem recommendation. No new JSP identifier is assigned by this submission.

# Statement and significance

Let E = {n in the natural numbers: n is odd and n is not p + 2^k for any prime p and integer k >= 0}. The checked conclusion is that there do not exist sets A, B with E = A union B, A = {a + md : m >= 0} for some a >= 0 and d > 0, and lim(N -> infinity) #{x < N : x in B}/N = 0.

This is the original one-progression question. Chen's later v3 abstract states a stronger finite-union result; that stronger theorem is outside this package's scope. The inspected paper discusses Erdős's 1950 exceptional-progression construction; this package does not assign a verified proposal date to the conjecture.

The incremental contribution connects the prior formal proof's no-infinite-progression predicate to the actual asymptotic density definition, and handles the k = 0 boundary. These bridges close an explicit statement-alignment gap. They do not establish new mathematics or global first-formalization priority.

# Known results and verification evidence

Mathematical credit remains with Yong-Gao Chen. The prerequisite's header credits Gemini 3.1 Pro, Antigravity, and Daniel Chin for its formalization. The separate Formal Conjectures statement credits Chin using Aristotle; both attributions are disclosed.

Pinned prior proof:
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos16.lean

New proof and reproducible project:
https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/171bf6b5bbb17ef64aeb795ebaad5c17b5901c31/projects/erdos-16-density

Reference statement:
https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/16.lean

Completed CI run (success):
https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171372534

The pinned run passed Lean build with warnings as errors, three kernel replays, eight axiom audits, dependency checks, rejection of a false arithmetic control, and NaNoda checking of 12,098 declarations. Artifact 10477031441 is 7,741,190 bytes, SHA-256 `90c200c6662f1e859dc2ab7144c5a0ee63ed21c4f1be02a824b357154b4eaf3a`; it expires 2026-12-16T01:39:05Z. The downloaded archive and its source hashes were checked. Compact logs and the detailed verification report accompany this recommendation. These are contributor-run checks, not organizer approval.

The existing proof is fetched unchanged with a SHA-256 check rather than redistributed. Its negative-decomposition statement uses a weaker condition than density zero on the remainder; this supplement proves the implication needed to recover the stated problem. It does not allege a false upstream theorem.

# Related records and conflicts

This is a self-submission prepared with OpenAI ChatGPT/Codex assistance. The proposed contributor placeholder `RECIPIENT-ERDOS16-KZ-A` is unconfirmed. No relationship to the prior proof authors is claimed. No candidate status, recipient confirmation, award grade, prize share, or payment entitlement is asserted.

Please assess whether this problem can enter the catalog and whether this formalization increment is substantive and eligible for consideration. The public rules do not guarantee eligibility for this contribution. Any award attribution must preserve the prior mathematical and formalization credits.

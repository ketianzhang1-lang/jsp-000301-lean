# JSP-000250: our prime upper bound and the complete unit-fraction estimate

We retain our original prime-denominator obstruction and explicit upper bound,
and connect them to a fully attributed lower-bound development. The endpoint
is `JSP000250.jsp_000250` in [JSP000250Complete.lean](JSP000250Complete.lean).

Let t(N) be the least positive integer that cannot be the smallest denominator
of a sum of distinct positive unit fractions equal to one, with all denominators
at most N. For every sufficiently large natural N, the endpoint states

    (1/1000000) * N / (log N * (log log N)^3 * (log log log N)^20)
        < t(N) <= 128 * N / log N.

This is the full quantitative resolution in Liu and Sawhney's
[Theorem 1.6](https://arxiv.org/html/2404.07113v1), with explicit constants
and exponent. It is not an exact asymptotic equivalent or an all-small-N formula.
We also provide strictly increasing denominator sequences for every positive
least denominator in the lower range.

## Our contribution

We retain all eleven public lemmas/theorems of the original upper proof unchanged.
Our ten added theorems identify the finite-set and increasing-sequence models,
prove equality of the least-exception functions for all N including zero,
transport lower-range witnesses including denominators one and two, derive a
strict lower bound and combine it with our original upper argument.

We also provide the full 75-module lower-proof closure, recorded compatibility
port, statement correspondence and reproducible checking. The work was prepared
under GitHub account `ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance.

The lower formalization is reused from
[plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos294.lean),
whose entry credits Codex and GPT-5.6 Sol. Mathematical and dependency authors
retain credit; [PROVENANCE.md](PROVENANCE.md) separates our contribution from
imported work. We make no first-formalization or award-entitlement claim.

## Verification status

The complete integration is undergoing compilation and audit. The earlier
upper-only verification is not evidence for this new endpoint. Exact completed
results and proof identification will be recorded in [VERIFICATION.md](VERIFICATION.md).

## Reproduce

Repository: `ketianzhang1-lang/jsp-000301-lean`; branch:
`jsp-000250-prime-obstruction`. Check out the full proof SHA in the final
verification record. Lean is pinned to 4.34.0 and Mathlib to
`5ed2965256430c3649e86755f9576b54eca72435`, with all nine dependencies locked.
Git, Python 3, elan and Rust/Cargo are required:

```sh
cd projects/jsp-000250
elan toolchain install "$(cat lean-toolchain)"
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The bootstrap checks original and ported source hashes. The verifier compiles
78 modules with warnings as errors, audits 21 theorem closures, replays every
proof-module prefix, checks dependencies and rejects a false-arithmetic control.
NaNoda checks all selected closures allowing only `propext`, `Classical.choice`
and `Quot.sound`. These contributor checks are not independent human review.

The optional local `verify.sh --resume` requires successful logs and fingerprints
of source plus all transitive local imports. The public workflow runs without resume.

## Proof guide

- [Original upper proof](JSP000250.lean).
- [Exact model bridge and complete endpoint](JSP000250Complete.lean).
- [All 21 axiom audits](AuditComplete.lean).
- [Original-statement correspondence](STATEMENT_FIDELITY.md).
- [Pinned source closure and compatibility edits](UPSTREAM.json).
- [Contribution and attribution](PROVENANCE.md).

The target is existing awards PR #354. Acceptance, priority and contribution
eligibility remain for maintainer review.

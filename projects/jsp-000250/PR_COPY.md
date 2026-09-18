# PR title

JSP-000250: complete unit-fraction bounds with our prime-obstruction upper proof

# PR body

## Submission type

- [ ] Mathematical solver information
- [x] Lean proof or formalization author information

## Problem and proposed change

We submit the complete quantitative resolution of **JSP-000250 / Erdős 294**. This replaces the earlier upper-bound-only scope of PR #354.

Let `t(N)` be the least positive integer that cannot be the smallest denominator in a sum of distinct positive unit fractions equal to one, with every denominator at most `N`. Our endpoint proves, for every sufficiently large natural `N`,

```text
(1/1000000) * N / (log N * (log log N)^3 * (log log log N)^20)
    < t(N) <= 128 * N / log N.
```

This is the complete two-sided estimate in Liu and Sawhney's [Theorem 1.6](https://arxiv.org/html/2404.07113v1), with explicit constants and triple-logarithm exponent. The threshold is existential. We also provide strictly increasing denominator sequences for every positive initial denominator in the lower range, including one and two. The source result is an eventual comparison estimate, not an exact asymptotic equivalent or a formula for every small cutoff.

The catalog diff updates only **Lean proof** and **Attribution basis** for JSP-000250. The old proof packet is removed from the awards repository; its history remains available. We do not change the entry's existing mathematical status or eligibility fields.

## Our contribution and attribution

We retain our original eleven-theorem upper-bound development byte-for-byte, including denominator clearing, the prime obstruction, existence and minimality of the first exception, the explicit logarithmic upper bound, and its unconditional Big-O formulation.

Our ten added theorems establish the exact finite-set/increasing-sequence correspondence, identify the least exceptions for every natural cutoff including zero, transport lower-range witnesses, handle denominators one and two, derive a strict lower bound, and combine it with our original upper proof. The upper direction of the final endpoint invokes our retained theorem.

We prepared our contribution under GitHub account `ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance. We provide the full pinned source closure, a recorded compatibility port, statement correspondence, and reproducible verification.

The lower-bound mathematics is due to Yang P. Liu and Mehtaab Sawhney. We reuse the lower formalization and its 75-module transitive closure from [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos294.lean), whose entry credits Codex and GPT-5.6 Sol. Author notices, available licenses, immutable input hashes and exact compatibility edits are retained or recorded. The closure includes the `UnitFractions` and `PrimeNumberTheoremAnd` developments. Erdős–Graham, Liu–Sawhney and the other mathematical and library contributors retain their respective credit.

We claim our original upper formalization, exact model integration and verification work. We do not claim authorship of the imported lower proof, new informal mathematics, first-formalization priority or independent human verification. [Our provenance record](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5e102c18cde266e4bd9e5bff01e44685fcc03ec7/projects/jsp-000250/PROVENANCE.md) distinguishes these roles.

## Proof source

```json
[
  {
    "repository": "https://github.com/ketianzhang1-lang/jsp-000301-lean",
    "branch": "jsp-000250-prime-obstruction",
    "commit": "e2f4c737ad4c2c9d7f4dcbfd4214fd2f2c96c876"
  }
]
```

- Complete endpoint: [`JSP000250.jsp_000250`](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/e2f4c737ad4c2c9d7f4dcbfd4214fd2f2c96c876/projects/jsp-000250/JSP000250Complete.lean).
- Quantified source formulation: `JSP000250.liu_sawhney_resolution`, in the same file.
- [README and build instructions](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5e102c18cde266e4bd9e5bff01e44685fcc03ec7/projects/jsp-000250/README.md).
- [Original-statement correspondence](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5e102c18cde266e4bd9e5bff01e44685fcc03ec7/projects/jsp-000250/STATEMENT_FIDELITY.md).
- [Verification record](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5e102c18cde266e4bd9e5bff01e44685fcc03ec7/projects/jsp-000250/VERIFICATION.md).

The final theorem has no unproved Fourier, density, smoothness or representation premise. All ingredients used by the lower proof are supplied by the pinned closure. The exact representation and least-exception bridges are proved, rather than assumed.

```sh
git clone --branch jsp-000250-prime-obstruction https://github.com/ketianzhang1-lang/jsp-000301-lean.git
cd jsp-000301-lean
git checkout e2f4c737ad4c2c9d7f4dcbfd4214fd2f2c96c876
cd projects/jsp-000250
elan toolchain install "$(cat lean-toolchain)"
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

Lean is pinned to 4.34.0; Mathlib and all nine dependency revisions are locked. The independent checker script also requires Rust/Cargo and pins lean4export and NaNoda.

The [complete hosted verification run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35362198703) passed on 2026-09-18 for the exact proof commit above: all **78 modules** compiled with warnings treated as errors; all **21 axiom audits**, the proof-module kernel replays and the false-arithmetic negative control passed. Independent NaNoda checked **75,850 declarations with no errors**, with a hard-error allowlist containing only `propext`, `Classical.choice` and `Quot.sound`. The checked theorem closures do not rely on `sorryAx` or replacement axioms. The tested source, logs, printed targets and exported proof closure are archived in the run artifact.

Local awards-repository validation, link/history checks, data consistency checks and all 22 unit tests also passed. The upstream PR workflows currently report `action_required` and need maintainer attention before they run. These repository checks validate the submission format. We request maintainer review of the complete statement and our disclosed contribution; machine verification does not establish award eligibility or organizer approval.

## Submission checklist

- [x] We changed only Lean proof information and supporting attribution in the relevant catalog.
- [x] We supplied the evidence required for this change.
- [x] The submitted Lean development covers the complete stated result at the specified commit, without `sorry`, `admit` or replacement axioms standing in for proof steps.
- [x] This PR contains no proof source files, archives, binaries or vendored dependencies.
- [x] The named branch contains the full proof commit selected for review.

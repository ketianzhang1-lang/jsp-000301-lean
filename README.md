# JSP-000301: complete counterexample formalization and reproducible verification

We formalize the complete negative answer to the catalog question: if two consecutive positive integers are powerful, must at least one be a square? We prove that **12167 and 12168 are consecutive powerful positive integers and neither is a square**, then export the negation of the universal assertion.

## Our formalization contribution

Our contribution, recorded under GitHub account `ketianzhang1-lang`, comprises the Lean implementation of the explicit counterexample, the supporting primality, divisibility and non-square proofs, the final logical negation, and the pinned verification project. We developed this implementation with OpenAI ChatGPT assistance using Mathlib definitions and proof-producing tactics. [PROVENANCE.md](PROVENANCE.md) identifies the mathematical source and contribution boundary.

## Complete statement and theorem locations

In [JSP000301.lean](JSP000301.lean), `Powerful n` means that the square of every prime divisor of n divides n, and `PerfectSquare n` means that n is a natural-number square.

- `JSP000301.jsp_000301_counterexample` supplies a positive witness with both powerfulness proofs and both non-square proofs.
- `JSP000301.jsp_000301_disproved` negates the full universal statement.

The witness uses 12167 = 23^3 and 12168 = 2^3 * 3^2 * 13^2. A counterexample completely resolves this yes/no question. The separate counting question on Erdős Problem 365 is outside the stated JSP-000301 catalog entry. See [STATEMENT_FIDELITY.md](STATEMENT_FIDELITY.md).

## Pinned proof and verification

- Repository: https://github.com/ketianzhang1-lang/jsp-000301-lean
- Branch: `main`
- Verified proof commit: `e1a17b0d6728b9d4929d1d4abd3721a27377369a`
- Lean 4.34.0; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`, with the committed transitive dependency manifest.
- [Successful verification run 35131699133](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35131699133).

The build with warnings treated as errors, bundled Lean checker and nine-declaration project axiom audit passed. NaNoda checked 188,335 declarations with no typechecker errors; it also reported one pretty-printer error. [VERIFICATION.md](VERIFICATION.md) preserves this distinction, the separate successful axiom audit and the checker settings.

## New strict verification — 2026-09-19

[Run 35413514755](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35413514755) succeeded at verification commit `26282f3afe1d23d35afda21cbecbc2f918043c6a` on branch `jsp-000301-strict-verification-20260919`. It verifies unchanged proof source from `e1a17b0d6728b9d4929d1d4abd3721a27377369a`.

- Warning-as-error build, bundled kernel replay, eight explicit public-target axiom reports, nine actual dependency revisions, and rejection of the false-arithmetic control passed.
- NaNoda checked **3,487 declarations** from the eight target dependency closures with no errors. Its allowlist contains only `propext`, `Classical.choice`, `Quot.sound`; `unpermitted_axiom_hard_error=true`. The script also requires nonempty printed statement output, which passed.
- The source, lakefile, toolchain and dependency manifest are byte-identical to the original selected proof. The eight explicit targets comprise two definitions and six proved statements; the previous automatic namespace audit counted nine declarations.
- Artifact `10575146525`, `jsp-000301-strict-evidence`, has GitHub-reported ZIP digest `sha256:29df04162583e549491707ac6948c8ba959d78e5be5a0c78b830409053c11937`. This ZIP digest was not recomputed from downloaded bytes here.

The new check addresses the selected theorem closures using a strict export. It is not a repeated 188,335-declaration whole-environment export. The old printer error and broader environment settings remain recorded below as historical evidence. All runs are contributor-operated, not independent human certification.

To reproduce the new result at the repository root:

```bash
git checkout --detach 26282f3afe1d23d35afda21cbecbc2f918043c6a
lake exe cache get
python3 scripts/verify_301_strict.py
bash scripts/verify_301_nanoda.sh
```

The pinned workflow installs the Lean toolchain and archives the tested inputs, checker configuration, compressed export and logs. The checker script requires Git and Rust/Cargo for the pinned independent checker. Preserve `lake-manifest.json`.

## Reproduce the original proof snapshot

```bash
git clone https://github.com/ketianzhang1-lang/jsp-000301-lean.git
cd jsp-000301-lean
git checkout --detach e1a17b0d6728b9d4929d1d4abd3721a27377369a
lake exe cache get
lake build --wfail
lake env leanchecker JSP000301
```

Keep `lake-manifest.json`; the workflow at the pinned commit specifies the additional NaNoda and axiom-audit commands and tool revisions. The original proof source and dependency pins remain unchanged. This branch additionally carries the separate strict verification scripts and workflow described above.

## Submission and requested credit

We submit this formalization through [awards PR #187](https://github.com/TheJustinSunPrize/awards/pull/187). The revised PR contains only catalog references; the proof and evidence are hosted in this repository. We request assessment of our formalization contribution. Mathematical credit for the counterexample remains with Solomon W. Golomb (1970). Contributor-run checking supports review; acceptance, priority and award eligibility remain for the organizers.

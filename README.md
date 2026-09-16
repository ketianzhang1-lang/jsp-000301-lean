# JSP-000301 — Lean 4 formalization

This repository formalizes the explicit counterexample recorded for Justin Sun Prize
problem **JSP-000301**:

> If two consecutive positive integers are powerful, must at least one be a perfect square?

The counterexample is the pair

- `12167 = 23^3`, and
- `12168 = 2^3 * 3^2 * 13^2`.

Both are powerful numbers, while neither is a perfect square because both lie strictly
between `110^2` and `111^2`.

## Formal statement

`JSP000301.lean` defines

```lean
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

def PerfectSquare (n : ℕ) : Prop :=
  ∃ m : ℕ, m ^ 2 = n
```

and proves:

- `JSP000301.jsp_000301_counterexample` — the explicit witness `n = 12167`;
- `JSP000301.jsp_000301_disproved` — the direct negation of the universal assertion.

See `STATEMENT_FIDELITY.md` for the statement-correspondence review.

## Toolchain

- Lean: `v4.34.0`
- Mathlib: `v4.34.0`

Both versions are pinned for reproducibility.

## Verification

The GitHub Actions workflow is configured to run:

1. `lake build --wfail`;
2. `leanchecker` on `JSP000301`;
3. the independent `nanoda` checker with `sorryAx` disallowed; and
4. `axiom-audit` using its default foundational-axiom allowlist.

A submission should not be made until all CI checks have completed successfully on a
public, pinned commit.

## Verify locally

With Lean/elan available:

```bash
lake update
lake exe cache get
lake build --wfail
```

## Attribution

This repository does **not** claim discovery of the mathematical counterexample. It
formalizes the counterexample already recorded by the Justin Sun Prize problem bank.
See `PROVENANCE.md` for formalization provenance and AI-assistance disclosure.

## Submission

After a green CI run, pin the full 40-character commit SHA and use
`SUBMISSION_ISSUE_DRAFT.md` to open the Prize repository's **Recommend a recipient**
issue form. Do not replace independent reviewer/signatory fields in the Prize's own
candidate records with self-attestation.

## Source problem

Justin Sun Prize problem-bank entry JSP-000301:
https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md

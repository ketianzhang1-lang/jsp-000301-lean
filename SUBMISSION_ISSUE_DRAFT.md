# Draft: Justin Sun Prize “Recommend a recipient” issue

Do not submit this draft until the proof repository has a green CI run and a pinned commit SHA.
Replace every `<...>` placeholder first.

## Suggested title

JSP-000301 — Lean formalization of the recorded counterexample

## Suggested body

**Problem:** JSP-000301 — “If two consecutive positive integers are powerful, must at least one be a perfect square?”

**Requested review:** Please review a Lean 4 formalization of the counterexample already recorded in the problem bank and consider the formalization contributor for the applicable formalization credit.

**Recipient:** `RECIPIENT--A` (identity/public profile to be confirmed through the Prize process)

**Contribution:** Lean formalization of the recorded counterexample for JSP-000301. This submission does **not** claim discovery of the mathematical counterexample.

**Pinned proof source:** `<PUBLIC_REPOSITORY_URL>/tree/<FULL_40_CHARACTER_COMMIT_SHA>`

**Lean source:** `<PUBLIC_REPOSITORY_URL>/blob/<FULL_40_CHARACTER_COMMIT_SHA>/JSP000301.lean`

**CI verification:** `<GREEN_GITHUB_ACTIONS_RUN_URL>`

**Toolchain:** Lean `v4.34.0`; Mathlib `v4.34.0`.

**Formal statement:** `JSP000301.jsp_000301_disproved`

The proof also contains `JSP000301.jsp_000301_counterexample`, with witness `n = 12167`.

### Statement correspondence

The formalization uses:

```lean
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

def PerfectSquare (n : ℕ) : Prop :=
  ∃ m : ℕ, m ^ 2 = n
```

and proves the negation of the universal assertion that any two consecutive positive powerful numbers contain a perfect square.

The counterexample is the same one recorded by the official problem bank:

- `12167 = 23^3`;
- `12168 = 2^3 * 3^2 * 13^2`;
- both are powerful;
- `110^2 < 12167 < 12168 < 111^2`, so neither is a square.

A detailed statement-comparison note is included in `STATEMENT_FIDELITY.md`.

### Verification performed by the proof repository CI

- `lake build --wfail`;
- Lean environment check with `leanchecker`;
- independent checking with `nanoda`, with `sorryAx` disallowed;
- axiom allowlist audit over namespace `JSP000301`.

### Attribution / provenance

The mathematical counterexample is pre-existing and is already recorded by the Prize problem bank. The submitted contribution is the Lean formalization. The formalization was prepared with AI assistance from OpenAI ChatGPT; no third-party Lean proof source was copied. See `PROVENANCE.md`.

### Official problem-bank source

https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md

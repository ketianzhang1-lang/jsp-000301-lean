# Statement fidelity for JSP-000301

## Natural-language problem

The Justin Sun Prize problem bank states JSP-000301 as:

> If two consecutive positive integers are powerful, must at least one be a perfect square?

The problem-bank record marks the statement as disproved by the consecutive pair
`12167 = 23^3` and `12168 = 2^3 * 3^2 * 13^2`, and notes that both values lie
strictly between `110^2` and `111^2`.

Source:
https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md

## Formal definitions

The Lean file defines

```lean
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

def PerfectSquare (n : ℕ) : Prop :=
  ∃ m : ℕ, m ^ 2 = n
```

`Powerful n` directly formalizes the standard condition used by the problem-bank
review note: every prime divisor of `n` occurs to exponent at least two, equivalently
`p^2 ∣ n` for every prime `p ∣ n`.

`PerfectSquare n` says exactly that `n = m^2` for some natural number `m` (the equality
is written in the symmetric orientation `m^2 = n`).

## Formalized claim

The principal theorem is

```lean
theorem jsp_000301_disproved :
    ¬ (∀ n : ℕ,
      0 < n →
      Powerful n →
      Powerful (n + 1) →
      PerfectSquare n ∨ PerfectSquare (n + 1))
```

This is the direct logical negation of the universal assertion implicit in the yes/no
question. The separate theorem `jsp_000301_counterexample` provides the explicit witness
`n = 12167`.

## Scope

This formalization addresses only the scoped yes/no question recorded as JSP-000301.
It does not claim to formalize any separate counting or classification question about
consecutive powerful numbers.

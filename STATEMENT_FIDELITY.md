# Statement fidelity: JSP-000393 constructive component

## Exact Lean statements

```lean
theorem family_counts (k : ℕ) :
    (family k).support.card = 13 ^ k ∧
    ((family k)^2).support.card = 12 ^ k

theorem arbitrarily_sparse_squares (M : ℕ) :
    ∃ p : ℤ[X], M * (p ^ 2).support.card < p.support.card
```

The definitions use Mathlib's ordinary univariate integer polynomials, `Polynomial.support`, multiplication and square. `Polynomial.expand ℤ 25` is the substitution x ↦ x^25. Every natural parameter is quantified without a finite cutoff. Coefficients, finite support, degree bounds, uniqueness of separated exponents and noncancellation are proved inside Lean.

## Relation to the catalog

The catalog asks about bounds relating the number of terms of a polynomial to those of its square. Erdős 485's main lower-bound question is whether the attained minimum square support tends to infinity as original support tends to infinity. This development does not prove that statement. It supplies a constructive upper-bound phenomenon along original support sizes 13^k and an unbounded ratio theorem. Both counts tend to infinity, so the construction is fully consistent with Schinzel's theorem.

The seed is exactly the polynomial P_12 on p. 86 of Coppersmith–Davenport (1991), independently re-expanded and checked here. The amplification uses base 25 to avoid exponent collisions even after squaring. It does not assert that F_k is a complete polynomial (for k > 1 it has gaps), that all support sizes are attained, that the 13/12 seed is minimal, or that any asymptotic exponent is optimal. The formal coefficient ring is ℤ. No separate machine-checked extension to arbitrary coefficient fields is claimed.

## Existing formalization

Official issue #44 registers the plby implementation of Schinzel's theorem at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, entry `src/latest/ErdosProblems/Erdos485.lean`. Its entry theorem is `Erdos485.erdos_485 : Tendsto f atTop atTop`. This work neither replaces nor imports that project. No first-formalization priority for JSP-000393 is claimed. The entry and registration were checked for scope; the entire upstream project was not exhaustively searched for every possible overlapping auxiliary construction.

This comparison is by the submitter, not an independent referee attestation. Reviewers must decide whether the additional scope is relevant and eligible for any credit.

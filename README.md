# JSP-000393: an explicit sparse-square family

This project formalizes a **known constructive component** related to JSP-000393 / Erdős 485. It proves exact nonzero-coefficient counts for a family of integer polynomials, and proves that the ratio of original support to squared support is unbounded.

It does **not** prove Schinzel's complete lower-bound theorem for the minimum square support, nor the stronger all-N complete-polynomial results of Coppersmith and Davenport. No new mathematical discovery, first formalization, official verification, or award is claimed.

## Verified mathematical statements

Let T(P) be the cardinality of `Polynomial.support`, i.e. the number of nonzero coefficients of the ordinary univariate polynomial P.

The Coppersmith–Davenport seed is

    S(x) = (1 + 2x - 2x² + 4x³ - 10x⁴ + 50x⁵ + 125x⁶)(1 - 110x⁶).

The Lean proof checks T(S) = 13 and T(S²) = 12 by exact polynomial identities and support calculations. Define

    F₀(x) = 1
    Fₖ₊₁(x) = S(x) Fₖ(x²⁵).

For every natural k, `JSP000393.family_counts` proves

    T(Fₖ) = 13ᵏ,   T(Fₖ²) = 12ᵏ.

`JSP000393.arbitrarily_sparse_squares` proves, for every natural M,

    ∃ P ∈ ℤ[x], M T(P²) < T(P).

The witness is F₁₂M. For M = 0 the witness is the constant polynomial; the meaningful arbitrarily large factors are covered for all M ≥ 1. The strict inequality excludes P = 0.

## Why the construction works

If deg(P) < b, then all exponents i + bj coming from P(x)Q(xᵇ) are distinct: reduction modulo b recovers i, and then j. Over the integers the product of two nonzero coefficients is nonzero. Thus the term counts multiply. The proof applies this argument both to S, of degree 12, and S², of degree 24, with b = 25.

The final theorem uses the proved inequality (k + 12)12ᵏ ≤ 12·13ᵏ. Taking k = 12M gives the desired strict comparison. No asymptotic approximation or external arithmetic certificate is assumed.

## Reproduction

Install Lean via elan and use the committed toolchain and dependency manifest:

```sh
lake exe cache get Mathlib.Algebra.Polynomial.Expand Mathlib.Tactic
lake build --wfail
lake env leanchecker -v JSP000393
```

Lean is pinned to v4.34.0 and Mathlib to `5ed2965256430c3649e86755f9576b54eca72435`. Do not run `lake update` when reproducing the pinned source.

The local build and bundled leanchecker passed. The two main theorem axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry`, `admit`, `native_decide`, or added axiom in the proof. The separate GitHub workflow requests compilation, bundled leanchecker, NaNoda and the strict project axiom audit. A workflow definition alone is not a passing-run claim.

See [statement comparison](STATEMENT_FIDELITY.md), [provenance](PROVENANCE.md), and [local verification evidence](evidence/local-verification.json).

## Sources and prior work

- Coppersmith, D. and Davenport, J. H. *Polynomials whose powers are sparse*, Acta Arithmetica 58(1), 79–87 (1991), especially p. 86 for this exact seed and pp. 80–81 for product constructions. [Primary PDF](https://matwbn.icm.edu.pl/ksiazki/aa/aa58/aa5816.pdf); [author's institution record](https://researchportal.bath.ac.uk/en/publications/polynomials-whose-powers-are-sparse/).
- Erdős, P. *On the number of terms of the square of a polynomial*, Nieuw Arch. Wiskunde (2) 23, 63–65 (1949), cited by Coppersmith and Davenport for the earlier sublinear upper-bound phenomenon.
- [Official JSP-000393 catalog](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000393).
- [Existing verification registration, issue #44](https://github.com/TheJustinSunPrize/awards/issues/44), links plby/lean-proofs' Schinzel lower-bound formalization. That existing full problem result is explicitly acknowledged. This submission asks only for review of the additional constructive scope; it makes no claim to its contributors' work.

Eligibility and any award decision remain with the Prize. Review status is pending.

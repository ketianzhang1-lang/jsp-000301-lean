# JSP-000912 / Erdős 1099: complete divisor-gap formalization

We provide a **complete Lean formalization of the main divisor-gap existence theorem**, using an explicit multiscale construction, with OpenAI assistance.

## Our formalization contribution

1. **Explicit witnesses beyond every cutoff.** We construct positive integers `N_K` with `K ≤ N_K` and a bound uniform in `K`.
2. **Complete divisor-list control.** We connect finite mixed-radix grids to actual consecutive divisors, prove weighted gap estimates, use complementary-divisor reflection, and telescope over the complete ordered divisor list.
3. **Every real exponent greater than one.** We adapt the construction parameter to `α−1`, covering exponents arbitrarily close to one and proving positive constants and positive witnesses.
4. **Two complete proof layouts.** We provide a standalone Mathlib-based proof and a five-module development, with automated checks that their proof bodies agree and that both export the required statement.
5. **Reproducibility and compatibility.** We preserve the original Lean 4.19 source, document the mechanical Lean 4.34 port, pin dependencies, and provide build, kernel replay, exact-type, axiom and NaNoda checks.

## Main theorem and construction

For the complete ascending list of positive divisors of a positive integer n, define

`h_alpha(n) = sum_i (d_(i+1) / d_i - 1)^alpha`.

The main declaration, **JSP912.jsp_000912_full** in [FullProof.lean](FullProof.lean), proves:

```lean
∀ α : ℝ, 1 < α → ∃ C : ℝ, 0 < C ∧
  ∀ M : ℕ, ∃ n : ℕ, 0 < n ∧ M ≤ n ∧ JSP912.hAlpha α n ≤ C
```

The conventional quantifier form is exported as `JSP912.erdos_1099`. The same proof is supplied in five modules ending in [JSP912/Main.lean](JSP912/Main.lean).

We formalize an explicit multiscale construction using finite mixed-radix divisor grids, dyadic bounds, weighted gap decay, complementary-divisor reflection, and telescoping over every adjacent pair in the complete divisor list. For any integer r ≥ 1 with r(α−1) ≥ 4, the construction gives positive integers N_K satisfying

`K ≤ N_K` and `h_alpha(N_K) ≤ 64 (16r(r+1)+2)^2`.

The parameter K is unrestricted, including zero. Choosing K = M supplies a positive witness beyond every requested cutoff. See [PROOF.md](PROOF.md) for the construction and mathematical argument.

This proves the full main existence question. The separate factorial and least-common-multiple variants are outside the submitted theorem.

## Pinned environment and reproduction

- Lean: `leanprover/lean4:v4.34.0`.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
- All dependency revisions: [lake-manifest.json](lake-manifest.json).
- Public proof branch: `jsp-000912-complete-proof`.
- Organizer review: [PR #691](https://github.com/TheJustinSunPrize/awards/pull/691).

Check out the full 40-character proof commit cited in the catalog or PR. From `projects/jsp-000912`, with Elan and the pinned toolchain installed:

```bash
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

Keep the committed manifest; do not run `lake update` when reproducing this snapshot.

The first script builds the standalone proof and all five modules with warnings as errors, replays all six modules with the bundled Lean checker, checks exact theorem and divisor-list types in both layouts, audits seven transitive axiom closures in each layout, checks actual dependency revisions, and requires rejection of an invalid arithmetic statement. It also checks that the standalone and modular proof bodies agree.

The second script exports the seven audited targets and their dependency closures to pinned NaNoda, allowing only `propext`, `Classical.choice` and `Quot.sound`.

The [verification workflow](../../.github/workflows/jsp-000912.yml) runs these checks and publishes the checked source, commit identifier, manifest and logs. Our [public verification run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35265836287) succeeded at proof snapshot `bf99214b3104d89c628abb9c824a56d89a6bd6fe`, including NaNoda verification of 17,954 declarations. This README revision changes documentation only; the Lean proofs, dependencies, verification scripts, workflows and source hashes are unchanged.

## Source recovery and compatibility port

The recovered Lean 4.19 source and original contributor-side logs are preserved at [commit 9074d0cebd4e132a6c1fa71c0817693246935398](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/9074d0cebd4e132a6c1fa71c0817693246935398/projects/jsp-000912). Every recovered archive file matched its recorded SHA-256 checksum.

The current source is a mechanical Lean/Mathlib 4.34 compatibility port. See [PORT.md](PORT.md) and [LEAN4_34_PORT.patch](LEAN4_34_PORT.patch). No mathematical definition, theorem statement, construction or hypothesis was changed. Historical Lean 4.19 receipts remain under [evidence/original-4.19](evidence/original-4.19) and must not be presented as receipts for the current version.

<a id="attribution-and-prior-work"></a>

## Mathematical source and requested credit

The affirmative mathematical result is due to Michael D. Vose, “Integers with consecutive divisors in small ratio,” Journal of Number Theory 19(2), 1984, 233–238, [DOI](https://doi.org/10.1016/0022-314X(84)90107-0).

We request credit for our explicit construction's Lean implementation, full divisor-list integration, compatibility port and reproducible verification. We developed the implementation with OpenAI assistance; the project imports Mathlib and our own proof modules.

Our submission concerns formalization and verification work. We make no mathematical-discovery or first-formalization priority claim. Organizer acceptance and eligibility remain subject to review.

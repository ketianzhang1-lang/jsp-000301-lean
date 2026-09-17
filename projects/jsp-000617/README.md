# JSP-000617 / Erdős 749: upper-density variant

This project formalizes the **upper-asymptotic-density variant**, not the original
lower-density problem. The final theorem is `JSP000617.upper_density_variant` in
`JSP000617Upper.lean`:

For every real ε > 0 there is a set A ⊆ ℕ such that the upper asymptotic density of
A+A is at least 1−ε and there is one natural constant C with r_A(n) ≤ C for every n.
Here r_A counts ordered pairs (a,b) ∈ A×A with a+b=n, including a=b.

The completed theorem passed local Lean 4.34.0 compilation and its transitive axiom
report contains only `propext`, `Classical.choice`, and `Quot.sound`. The workflow
`JSP-000617 upper-density verification` performs a fresh locked build, Lean's
checker, an axiom audit, and independent checking by Nanoda. Consult the workflow
result for the exact committed version; local compilation alone is not a claim
that the remote workflow passed.

## Scope and attribution

The mathematical upper-density result is attributed to Aron Bhalla, with disclosed
GPT-5.4 assistance, on the original problem page. Terence Tao explained the
finite-field/parabola and separated-scale architecture in the discussion.
This project supplies a Lean implementation under Ketian Zhang's direction with
OpenAI ChatGPT assistance. It preserves the authors' and Mathlib contributors'
credit. It claims neither a solution of the original lower-density problem nor a
new mathematical discovery, first-formalization priority, prize eligibility,
organizer acceptance, or payment.

Sources:
- https://www.erdosproblems.com/749
- https://www.erdosproblems.com/forum/thread/749
- https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000617
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/749.lean

The official catalog recorded progress on the upper-density variant and marked the
problem ineligible to claim when checked on 2026-09-17. Formalizing this variant
does not by itself establish eligibility for the full problem.

## Build and audit

Lean and Mathlib: 4.34.0. The exact dependency commits are in `lake-manifest.json`.

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The verification scripts reject proof holes, additional axioms, `native_decide`,
and `unsafe` declarations in the proof modules. They inspect the actual transitive
axioms of the final theorem. The independent exporter includes the final theorem
and its complete dependency closure. `PROOF.md` gives the mathematical argument;
`STATEMENT_FIDELITY.md` explains the exact definitions and quantifiers.

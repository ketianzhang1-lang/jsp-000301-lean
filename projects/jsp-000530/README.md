# JSP-000530: two-axis counterexample to Erdős 654

This project formalizes the negative answer to the following statement:
if a planar set of n points has no four points on a circle, must some point
determine at least (1-o(1))n distinct distances to the other points?

For every natural m, `counterexample_family` produces a finite subset of the
complex plane with exactly 4m points. Every Euclidean circle meets it in at
most three points. Every point determines fewer than 3m distinct distances
to the other points. `not_asymptotically_all_distances` formally negates the
uniform epsilon/N formulation of the proposed asymptotic claim.

The plane is Mathlib's complex plane with its standard Euclidean distance.
The circle predicate uses the actual metric sphere equation `dist p z = r`,
with arbitrary real centers and radii. The distance count excludes the base
point. The construction works for every m; it is not a finite computation.

## Construction

Use the points `(±2(i+1),0)` and `(0,±(2i+1))` for `0 ≤ i < m`.
The two-axis idea is due to Aletheia (Google DeepMind), as reported by Feng
et al., *Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on
the Erdős Problems*, arXiv:2601.22401v3, Section 3.1:
https://arxiv.org/abs/2601.22401v3

This implementation uses even and odd coordinates in place of the source's
powers of two and three. It is independently written formalization work,
assisted by OpenAI ChatGPT; no new mathematical solution or global first
formalization priority is claimed.

A circle meets each axis at most twice. If it met two points on each axis,
the products of the two signed coordinates would agree. One product is
even and the other odd, a contradiction. Opposite points on the other axis
have the same distance from a given point. Thus there are at most m cross-axis
distances and at most 2m-1 same-axis distances.

## Scope and attribution

This resolves the strong formulation with only the no-four-concyclic
hypothesis. It does **not** resolve the separate general-position problem
that also forbids three collinear points. Our configurations have many
collinear points. This distinction is stated in Section 3.1 of the source.
The source's raw model transcript contains an additional general-position
claim that the published paper explicitly rejects; it is not used here.

Prize record:
https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000530

Original problem page:
https://www.erdosproblems.com/654

The mathematical attribution remains with Aletheia and the published
authors. Mathlib and Lean retain their own licenses and credits. This
project uses the parent repository's MIT license for its new code.

## Reproduction

Pinned compiler: Lean 4.34.0. Pinned Mathlib commit:
`5ed2965256430c3649e86755f9576b54eca72435`.
The complete dependency lock is `lake-manifest.json`.

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

Verification scripts compile with warnings treated as errors, replay the
module through the bundled Lean checker, inspect six theorem dependency
closures for nonstandard axioms, check the dependency pins, and reject a
false-arithmetic negative control. The additional NaNoda script exports the
two final theorem dependency closures to a separately implemented checker
with only `propext`, `Classical.choice`, and `Quot.sound` permitted.

These are contributor-run checks. They do not substitute for independent
review of the statement, attribution, originality, or award eligibility.
The source code is public; GitHub Actions artifacts have finite retention.
No official approval, award, or payment entitlement is asserted.

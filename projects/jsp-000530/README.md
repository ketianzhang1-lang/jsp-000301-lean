# JSP-000530: two-axis formalization and the remaining scope requirement

We formalize the negative answer to the following statement:
if a planar set of n points has no four points on a circle, must some point
determine at least (1-o(1))n distinct distances to the other points?

For every natural m, `counterexample_family` produces a finite subset of the
complex plane with exactly 4m points. Every Euclidean circle meets it in at
most three points. Every point determines fewer than 3m distinct distances
to the other points. `not_asymptotically_all_distances` formally negates the
uniform epsilon/N formulation of the proposed asymptotic claim.

The plane is Mathlib's complex plane with its standard Euclidean distance.
The circle predicate uses the actual metric sphere equation `dist p z = r`,
with arbitrary centers in the complex plane and real radii. The distance count excludes the base
point. The construction works for every m; it is not a finite computation.

## Our formalization contribution

Our contribution, recorded under GitHub account `ketianzhang1-lang`, is an independently written Lean implementation using even and odd coordinates, its Euclidean-circle and distance-count proofs, the quantified asymptotic negation and the pinned verification package. We developed this implementation with OpenAI ChatGPT assistance. [PROVENANCE.md](PROVENANCE.md) records the mathematical source and contribution boundary.

## Further research and a scope correction

We have proved fifteen auxiliary Lean lemmas, including the exact distance-group slack identity, its uniform lower-bound reformulation, the perpendicular-bisector obstruction to preserving the existing pair equalities, and a proof that quadratic bending creates four concyclic points. [The research source and verification record](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/0cedcd9996abd02eb8b64393d4b879cbf8c6eceb/projects/jsp-000530/research/PROGRESS.md) are on branch `jsp-000530-general-position-research`. These lemmas do not complete the original problem.

Our earlier focus on the no-three-collinear condition did not describe the entire gap. [Erdős's 1987 paper, printed page 168](https://www.renyi.hu/~p_erdos/1987-27.pdf#page=2) also asks for a fixed positive improvement above the one-third lower bound. Our two-axis upper-bound example does not resolve that lower-bound question, with or without no three collinear points. The general-position upper-construction question also remains unresolved by this package.

## Complete-solution requirement

The current prize instructions require a complete solution of the original problem. Our code completely disproves the formulation with only the no-four-concyclic hypothesis, but it does not prove or disprove the historical formulation that additionally forbids three collinear points. The cited paper explicitly classifies its result as a partial solution of the multi-part problem (Section 3.1, Remark 3.1).

For m >= 2, our configurations have at least four points on each coordinate axis, so they fail the additional no-three-collinear hypothesis. This is a mathematical scope gap, not a missing build flag or README field. We cannot certify this package as resolving every original formulation. The missing formulation needs its own complete proof, or a source-backed maintainer determination that the catalog accepts the no-four-concyclic question as a separate complete target. The current material does not establish that determination.

## Construction

Use the points `(±2(i+1),0)` and `(0,±(2i+1))` for `0 ≤ i < m`.
The two-axis idea is due to Aletheia (Google DeepMind), as reported by Feng
et al., *Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on
the Erdős Problems*, arXiv:2601.22401v3, Section 3.1:
https://arxiv.org/abs/2601.22401v3

We use even and odd coordinates in place of the source's
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

## Pinned proof and verification

- Repository: https://github.com/ketianzhang1-lang/jsp-000301-lean
- Branch: `jsp-000530-two-axis`
- Verified proof commit: `fb8577233935d1ff4533418ff8ea33a4d7dab101`
- Project: `projects/jsp-000530`
- [Successful run 35169007348](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35169007348): source build, kernel replay, six axiom audits, dependency checks, negative control and NaNoda verification passed. NaNoda checked 13,905 declarations without errors.

The documentation-only scope update leaves the checked Lean source, manifests and scripts unchanged. [VERIFICATION.md](VERIFICATION.md) preserves the execution record. Successful checking confirms the stated formal theorem, not coverage of the additional collinearity condition.

## Reproduction

Check out the exact proof commit above and enter `projects/jsp-000530`.


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

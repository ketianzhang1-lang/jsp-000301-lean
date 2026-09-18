# JSP-000636: our complete threshold-estimate formalization

We formalize the original Erdős–Trotter threshold-estimate question for every
multiplicity **r ≥ 2**, on **every finite ground set**, and prove the sharp
leading growth **n₀(r)/r → 2**. Our development contains eight proof modules and
79 public theorems. The latest module adds eight original-statement and
relabeling theorems to the previously verified 71-theorem implementation.

We developed this implementation under GitHub account `ketianzhang1-lang`
with OpenAI ChatGPT/Codex assistance. We formalize known mathematics; we do
not claim mathematical discovery or first-formalization priority.

## The original question and its complete endpoint

[He and Tang, Problem 1.1](https://arxiv.org/html/2602.09803v1#S1) reproduces the
Erdős–Trotter question: for r>1 and all n above a threshold, an antichain with
exactly r sets at each occurring size can have r(n−3) members but cannot have
r(n−2); estimate the threshold n₀(r).

**`JSP000636.jsp_000636` in [OriginalQuestion.lean](OriginalQuestion.lean)**
combines all of the following without unproved extra assumptions:

- For every r≥2, an explicit cutoff N≤2r+4⌊√r⌋+7 works on every finite ground
  set with n>N elements: an exact-r antichain with r(n−3) members exists,
  and no such antichain with r(n−2) members exists.
- `threshold r` is the actual **least** eventual cutoff for the exact-r finite
  maximum, not a substituted upper cutoff.
- For every r≥4, **2r+2 ≤ n₀(r) ≤ 2r+4⌊√r⌋+7**.
- **n₀(r)/r → 2**, with the explicit relative-error estimate already proved in
  `Asymptotics.lean`.

The exact-r convention counts distinct subsets. Repeated copies cannot supply
multiplicity. The new injective relabeling results preserve containment, every
level count and total family size. Any concrete finite set can be used as the
ground type by taking its subtype. See [STATEMENT_FIDELITY.md](STATEMENT_FIDELITY.md).

The scope is the original **threshold-estimate question**, including all its
parameters, rather than formalization of every stronger result in the source
paper. The logarithmic error term, exact small-r values and the stronger
piecewise exact formula from PR #677 are not claimed here. Their absence does
not leave a parameter case unproved in the submitted estimates.

## Our contributions

- We separately implement the universal obstruction and the He–Tang lower-bound
  argument, together with a pair-label specialization of their construction.
- We formalize levelwise thinning, the exact-r and at-least-r finite maxima,
  and equality of those maxima.
- We prove the actual least-threshold correspondence, quantitative relative
  bounds and the ordinary real limit n₀(r)/r→2.
- We prove injective relabeling invariance for the entire family, antichain
  property and every level multiplicity, and transfer the result to arbitrary
  finite ground types.
- We provide the literal original existence/impossibility endpoint, full
  dependency pins, theorem audits, kernel replay and reproducible verification.

The seven earlier proof modules are unchanged from
`36da76e793678ee6a062f1703674fd3789334cbd`. This revision adds
`OriginalQuestion.lean` and its eight theorems. All proof steps are in this
implementation or its pinned Mathlib dependencies; no competing prize proof
is imported.

## Sources, prior work and contribution review

Mathematical credit remains with Yixin He and Quanyu Tang,
*An Erdős–Trotter problem on antichains with multiplicity r on each occurring
level*, [arXiv:2602.09803v1](https://arxiv.org/abs/2602.09803), and the classical
Erdős–Trotter observation. The lower-bound argument and general label method
follow that source. Our pair labels give a coarser square-root error term than
the paper's logarithmic error term, while retaining the sharp leading constant.

[PR #677](https://github.com/TheJustinSunPrize/awards/pull/677), by
`peilinliu66-dev`, already proposes a stronger exact formula. Its public
statements and source inventory were inspected; its full proof chain was not
independently rebuilt here. Its priority and attribution are retained in
[PROVENANCE.md](PROVENANCE.md). We claim neither that formula nor priority over
that submission.

We update existing [PR #382](https://github.com/TheJustinSunPrize/awards/pull/382)
with this complete original-threshold-estimate endpoint for maintainer review.
The awards PR contains catalog text and fixed proof references only.
Statement coverage, independent implementation, and an award decision are
separate questions. We request assessment of our concrete formalization
contributions; organizer acceptance and award eligibility remain pending.

## Reproduction

Lean is pinned to **4.34.0**, Mathlib to
`5ed2965256430c3649e86755f9576b54eca72435`, and all nine package revisions are
locked in `lake-manifest.json`. From `projects/jsp-000636` at the selected commit:

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first verifier compiles eight modules with warnings as errors, replays all
eight with Lean's kernel, audits all 79 public theorem closures, checks actual
dependency revisions and rejects a false-arithmetic control. The second exports
the final endpoints and their dependency closures to the separately implemented
NaNoda checker with a strict three-axiom allowlist. Keep the committed manifest.

[VERIFICATION.md](VERIFICATION.md) distinguishes executed local checks, public
workflow results and their limits. A configured checker is not a successful
check. Source code is Apache-2.0 (`LICENSE.LEAN`); mathematical sources retain
their authorship.

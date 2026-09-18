# JSP-000636: our threshold estimates and exact-multiplicity bridge

We formalize the Erdős–Trotter antichain threshold estimates for all multiplicities
`r ≥ 2`, and prove the sharp leading asymptotic **`n₀(r) / r → 2`**. Our new
`Asymptotics.lean` module adds ten theorems to the existing 61-theorem development.
We developed this implementation under GitHub account `ketianzhang1-lang` with
OpenAI ChatGPT/Codex assistance.

## Our contributions

- We implement a finite maximum using the original **exactly r sets at each
  occurring size** convention, and prove that it equals the at-least-r maximum.
- We prove that our threshold is the **least cutoff for this actual maximum**.
  It is not an arbitrary upper cutoff or an existence-only substitute.
- We prove a uniform relative-error estimate: for `m ≥ 1` and
  `r ≥ (8*m+8)^2`,
  `2*r ≤ n₀(r)` and `m*n₀(r) ≤ (2*m+1)*r`.
- We deduce the ordinary real limit `n₀(r)/r → 2`.
- We supply the exact-r extremal statement: for every `r ≥ 2`, an explicit
  threshold guarantees an antichain of exactly `r*(n-3)` sets, and every
  admissible antichain has at most this many sets.

The inherited pair-label construction proves
`2*r+2 ≤ n₀(r) ≤ 2*r+4*floor(sqrt(r))+7` for every `r ≥ 4`.
Threshold existence and the exact-r construction cover every `r ≥ 2`.
The six inherited proof modules are unchanged in this revision.

## Scope and submission status

The primary source, [He and Tang, Problem 1.1](https://arxiv.org/html/2602.09803v1#S1),
asks for estimates of the eventual threshold. The current theorems provide
unconditional all-parameter estimates and their leading asymptotic. The paper
also proves a sharper logarithmic error term and exact values at r=2 and r=3;
these are not formalized by this package.

A stronger exact-threshold submission already exists in
[awards PR #677](https://github.com/TheJustinSunPrize/awards/pull/677).
It states a piecewise formula covering every r≥2, including the exact small-r
values. We have inspected its public statements and source inventory but have
not independently rebuilt or certified its full proof chain. Our development
does not claim that stronger formula, first-formalization priority, or a new
mathematical discovery.

**This revision remains an estimate supplement to [our existing PR #382](https://github.com/TheJustinSunPrize/awards/pull/382).
It is not a claim that the prize organizers have accepted the original problem
as completely formalized by us.** The question of whether the all-parameter
estimate endpoint meets their full-original-problem requirement remains for
review. We do not mark the official catalog complete or request an eligibility
change based on this supplement.

## Exact endpoints

All theorem names below are in namespace `JSP000636`.

| File / theorem | Meaning |
| --- | --- |
| `Asymptotics.lean`, `exactExtremal_eq` | Equality of the exact-r and at-least-r maxima for every n and every positive r. |
| `threshold_exact_spec` | Least-threshold semantics for the original exact-r maximum. |
| `threshold_relative_bound` | Explicit natural-number relative-error estimate with cutoff `(8*m+8)^2`. |
| `threshold_ratio_tendsto` | Real limit `n₀(r)/r → 2`. |
| `exact_threshold_estimate` | Existence of an exact-r attaining family and the matching universal upper bound above an explicit threshold. |
| `jsp_000636_estimate` | Combined estimate endpoint, leastness, two-sided bounds and the limit. |

The ground set is `Fin n`, and families are finsets of finsets; duplicate sets
cannot supply multiplicity. `Antichain` is proved equivalent to Mathlib's
inclusion `IsAntichain`. `exactExtremal` and `extremal` are finite maxima over
all admissible families. `threshold r` agrees with the proved least threshold
for r≥2; its value below that domain is an explicitly immaterial convention.

## Mathematical sources and code provenance

Mathematical credit remains with Yixin He and Quanyu Tang,
*An Erdős–Trotter problem on antichains with multiplicity r on each occurring
level*, [arXiv:2602.09803v1](https://arxiv.org/abs/2602.09803), and with the
classical Erdős–Trotter observation. The lower-bound argument and general label
method follow that source. Our inherited construction specializes the labels
to two-element sets, giving the coarser square-root error term.

The new ten-theorem module derives consequences from our existing implementation
and Mathlib. See [PROVENANCE.md](PROVENANCE.md) for exact source lineage,
retained notices and the competing public submission.

## Reproduction

Lean is pinned to 4.34.0, Mathlib to
`5ed2965256430c3649e86755f9576b54eca72435`, and nine package revisions are locked
in `lake-manifest.json`. From `projects/jsp-000636`:

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first verifier compiles seven modules with warnings as errors, replays each
with Lean's bundled checker, audits all 71 theorem closures, checks all dependency
revisions and rejects a false-arithmetic control. The second exports the listed
endpoints and their complete dependency closures for the separately implemented
NaNoda checker with a strict three-axiom allowlist.

Executed results and their limitations are recorded in
[VERIFICATION.md](VERIFICATION.md). The workflow repeats these checks on pushes
to the existing proof branch. Source code is Apache-2.0 (`LICENSE.LEAN`);
mathematical sources retain their authorship.

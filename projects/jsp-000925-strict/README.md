# JSP-000925: strict gaps and existence of the derivative-root selector

We formalize strict outward monotonicity of derivative-root gaps and construct the derivative-root selector with interval-by-interval existence and uniqueness. Our contribution, recorded under GitHub account `ketianzhang1-lang`, comprises strict phase convexity, strict gap inequalities including the central even-degree case, the unconditional selector-existence endpoint, and the reproducible verification package. We developed these additions with OpenAI ChatGPT assistance using the credited upstream analytic infrastructure.

Let f be a nonzero real polynomial of degree N+1, N>0, whose roots are
`a + d*j`, j=0,...,N, with d>0. There is a unique derivative zero b_k in each
open interval `(a+d*k, a+d*(k+1))`. This package proves, for every admissible i,

    i+2 < N and N <= 2*(i+1) imply
    b_(i+1)-b_i < b_(i+2)-b_(i+1).

The gaps are reflection-symmetric. The equal central pair of gaps when N is
odd is not incorrectly made strict. Translation, spacing, leading coefficient,
and degree are arbitrary. Degrees with fewer than three derivative roots have
no strict gap comparison to make, but the existence and uniqueness conclusions
still apply. The polynomial itself and its actual derivative are used.

## Complete endpoint and our additions

The pinned prior `Erdos1114.erdos_1114` proves non-strict gap inequalities and
reflection symmetry, assuming an interlacing derivative-root selector.
Our `strict_gap_theorem` replaces the non-strict comparison by a strict one.
Our `exists_unique_strict_gaps` also constructs the selector using Rolle's theorem
and proves uniqueness in each interval. The upstream analytic infrastructure is
used explicitly and is not claimed as this contribution.

The complete endpoint is `JSP000925Strict.exists_unique_strict_gaps` in [JSP000925Strict.lean](JSP000925Strict.lean). It assumes only the original polynomial and progression hypotheses, with no assumed derivative-root selector or additional unproved analytic hypotheses. For N=1 or N=2, the gap-comparison conclusion is vacuous and the existence/uniqueness conclusions still apply. A linear polynomial has no derivative-root gaps to compare. Detailed source and dependency attribution is retained in [PROVENANCE.md](PROVENANCE.md).

## Proof route

The existing development expresses the derivative-root equation using a phase
function and three moments s,t,v satisfying `s>0`, `t^2<=s*v`, `s^3<=4*t`.
For positive u and nonnegative z, the numerator controlling phase convexity
is strictly positive. Multiplying its inner expression by s decomposes it into
five nonnegative terms, the first `(3*pi^2-16)*s*t` being strictly positive.
Thus the phase is strictly convex. Strict secant-slope comparisons give the
strict gaps; a separate midpoint argument handles the central even-N gap.
Affine normalization transfers the result to f. Rolle's theorem and the strict
decrease of the logarithmic derivative give existence and uniqueness.

## Pinned proof and verification

- Repository: https://github.com/ketianzhang1-lang/jsp-000301-lean
- Branch: `jsp-000925-strict-gaps`
- Verified proof commit: `7b545f0e021b06d434654b17881c11819f3ff1b7`
- Project: `projects/jsp-000925-strict`
- [Successful verification run 35168402594](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168402594): build, both module replays, eight axiom audits, dependency checks and negative control passed; NaNoda checked 50,927 declarations without errors.

[VERIFICATION.md](VERIFICATION.md) preserves the receipt and compact logs. This documentation update does not change the verified Lean source, bootstrap checksum, dependency pins or scripts.

## Reproduction

Check out the exact proof commit above and enter `projects/jsp-000925-strict`.


Lean 4.34.0 and Mathlib v4.34.0 (commit
`5ed2965256430c3649e86755f9576b54eca72435`) are pinned. All transitive Git
revisions are in lake-manifest.json.

    python3 scripts/bootstrap.py
    lake exe cache get
    bash scripts/verify.sh
    bash scripts/verify_nanoda.sh

Bootstrap retrieves the unchanged upstream prerequisite and checks its SHA-256.
It refuses to overwrite inconsistent bytes. The prerequisite is not redistributed
in this package. The first verification script builds with warnings as errors,
replays both modules using the bundled kernel, audits eight declarations against
the three standard foundational axioms, checks dependency pins, and rejects a
false arithmetic control. NaNoda independently checks the complete dependency
closures of both main results with a strict axiom allowlist.

See PROVENANCE.md for attribution and STATEMENT.md for exact interpretation.
Contributor-run verification is not organizer review. Network access and cached
Mathlib artifacts are used; no clean offline rebuild of all dependencies is claimed.

## Requested review

We submit the complete strict-gap theorem and our additional formalization work through [awards PR #342](https://github.com/TheJustinSunPrize/awards/pull/342). Our request concerns the concrete additions and verification above. Mathematical credit and the upstream analytic proof remain attributed in the provenance record; acceptance and contribution eligibility remain organizer decisions.

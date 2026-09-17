# JSP-000925: strict gaps and existence of the derivative-root selector

This is an incremental formalization supplement for JSP-000925 / Erdos 1114,
not a claim of a new mathematical solution or of first formalization.

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

## Incremental scope

The pinned prior `Erdos1114.erdos_1114` proves non-strict gap inequalities and
reflection symmetry, assuming an interlacing derivative-root selector.
Our `strict_gap_theorem` replaces the non-strict comparison by a strict one.
Our `exists_unique_strict_gaps` also constructs the selector using Rolle's theorem
and proves uniqueness in each interval. The upstream analytic infrastructure is
used explicitly and is not claimed as this contribution.

The comparison is against plby/lean-proofs commit
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, already registered in prize issue #24.
Please assess whether this incremental work is sufficiently substantive and
eligible. No global priority, award, or payment entitlement is asserted.

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

## Reproduction

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

# JSP-000714: an explicit Sidon construction and counting lower bounds

This is an independently written Lean formalization of a classical baseline
construction, prepared with OpenAI ChatGPT assistance. It is **partial scope**
relative to JSP-000714 / Erdos 861. It is not a new mathematical result, the
first formalization of the original problem, or a proof of its sharp counting
asymptotics. A broader public Lean development already exists; see below.

## Exact results

For every prime p > 2, put

    S_p = { 2*p*i + (i^2 mod p) + 1 : 0 <= i < p }.

The code proves that S_p has p elements, lies in {1,...,2*p^2}, and is a
Sidon set: a+b=c+d among elements implies equality of the unordered pairs.
Repeated summands are permitted, so three-term arithmetic progressions are
excluded too. Sidon subsets are counted once as finite sets.

Writing A(N) for the exact number of Sidon subsets of {1,...,N}, including
the empty set, the main endpoints prove:

* `prime_count_lower`: A(2*p^2) >= 2^p for every prime p > 2.
* `uniform_count_lower`: A(8*n^2) >= 2^n for every integer n >= 2.
* `all_cutoffs_lower`: A(N) >= 2^floor(sqrt(floor(N/8))) for every N >= 32.

These are unrestricted, quantified theorems, not finite experiments.
Bertrand's postulate supplies the prime for the uniform bound.

## Mathematical argument

The residue terms in a sum of two construction points have total less than
2p. Equality of point sums therefore implies equality of the index sums.
Reducing modulo p also equates the sums of their squares. In the field Z/pZ,
these two identities give 2(a-c)(a-d)=0. Since p is odd, one of a=c or a=d
holds modulo p; indices in [0,p) make that an ordinary equality. The other
index follows from the equality of sums. Every subset of S_p is Sidon, giving
2^p different sets. Choose n<p<=2n by Bertrand, then enlarge the ambient interval.

## Attribution and overlap

Mathematical credit for the modular-parabola construction remains with
Erdos and Turan and the classical Sidon-set literature. This implements the
standard construction with a positive translation. The original paper is
Erdos and Turan, *On a problem of Sidon in additive number theory, and on some
related problems*, Journal of the London Mathematical Society 16 (1941), 212-215,
[DOI](https://doi.org/10.1112/jlms/s1-16.4.212).

The [official catalog](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000714)
is broader than these lower bounds. The underlying
[Erdos 861](https://www.erdosproblems.com/861) asks finer questions involving
the maximum Sidon-set size f(N), A(N)/2^f(N), and the exponent of A(N).
This package does not answer those finer questions, prove the Saxton--Thomason
1.16 exponent, prove a counting upper bound, or count maximal Sidon sets.

A broader public development is already present in
[plby/lean-proofs at 8822f7d](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos861.lean)
and its Erdos862 dependency. Their notices credit the historical mathematical
authors and Codex / GPT-5.6 Sol for that formalization. That development was
consulted to identify scope and overlap; it is not imported or redistributed
here, and was not re-verified in this work. Its broader claims and priority
must not be attributed to this package. Our proof body was written independently
from the elementary argument above and uses Mathlib infrastructure.

## Reproduction

Pinned Lean and Mathlib: v4.34.0; exact package commits: `lake-manifest.json`.

```bash
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first script builds with warnings as errors, replays the module with
Lean's bundled checker, audits nine endpoints using only propext,
Classical.choice and Quot.sound, checks dependency commits, and requires
rejection of false arithmetic. The second uses pinned lean4export and NaNoda
to check the main theorem dependency closures with the same strict axiom
allowlist. Scripts are reproduction instructions; actual results must be
read from the associated run and verification receipt.

No `sorry`, `admit`, native evaluation, or additional mathematical axiom is used.
Source: Apache-2.0 (`LICENSE.LEAN`). Documentation: CC BY 4.0.

## Review status

Any consideration for a formalization contribution would be for this limited,
alternative implementation, with the existing broader work fully disclosed.
We do not assert substantive novelty, first priority, prize eligibility,
organizer verification, or payment entitlement. Recipient placeholder if
required: `RECIPIENT-JSP-000714-KZ-A`, confirmation pending.

# JSP-000737 / Erdos 886: the Erdos-Rosenfeld divisor bound

For every natural number n and every real C >= 0, this project proves

    #{d | d divides n, sqrt(n) <= d <= sqrt(n) + C*n^(1/4)} <= 1 + C^2.

The statement uses Mathlib's natural divisors and real powers. For positive n,
it concerns ordinary positive divisors; n=0 is covered by Mathlib's empty
`Nat.divisors 0` convention. The original eventual version follows immediately.

This is a complete formalization of that known component. It does not resolve
the full Ruzsa conjecture for every epsilon > 0, prove the separate infinite
four-divisor construction, or prove an absolute bound independent of C.

## Proof

Put r=sqrt(n). Send each divisor d>=r to the integer d+n/d. The factor sum
uniquely determines the larger factor: two roots of the same quadratic are the
factor pair, and both cannot lie strictly above r. Also

    (d+n/d) - 2r = (d-r)^2/d.

For r<=d<=r+C*n^(1/4), this is between 0 and C^2. Distinct factors therefore
map to distinct integers in [2r,2r+C^2]. Any real interval of length C^2 has at
most 1+C^2 integer points. Endpoints and zero are treated explicitly.

## Attribution

The mathematical result belongs to Paul Erdos and Moshe Rosenfeld,
*The factor-difference set of integers*, Acta Arithmetica 79.4 (1997), 353-359.
[Publication record](https://eudml.org/doc/206983).

The established target is in
[Formal Conjectures 886](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/886.lean).
`Compatibility.lean` preserves its mathematical type and applies the proof by
definitional equality. The source authors' Apache-2.0 attribution is retained.
The implementation was independently written for Ketian Zhang with OpenAI
ChatGPT assistance. No new mathematical discovery or global priority is claimed.

## Reproduction

Lean 4.34.0; Mathlib 5ed2965256430c3649e86755f9576b54eca72435.
All dependency revisions are locked in lake-manifest.json.

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first script builds with warnings treated as failures, replays the three
local modules through Lean's bundled checker, audits six targets against the
standard axiom allowlist, verifies dependency revisions, and checks rejection
of false arithmetic. The second exports the target dependency closure and
checks it with pinned NaNoda. Only completed logs establish actual pass status.

## Review request

Self-submission for scope, attribution, overlap and eligibility review.
Proposed recipient: RECIPIENT-JSP-000737-KZ-A (confirmation pending).
No award level, payout or independent human review is claimed. The catalog's
overall Open status remains unchanged.

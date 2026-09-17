# JSP-000303: quantitative powerful-part lower bound

This package formalizes a **known solved component** of Erdős Problem 367.
It does not solve the open `n^(2+o(1))` upper-bound question, and it does not
claim new mathematics, first formalization of the problem, eligibility, or an award.

For `B_2(n)`, the product of the exact prime-power factors of `n` whose exponents
are at least two, the package proves

```
for every k >= 3, infinitely many n satisfy
    product_{n <= m < n+k} B_2(m) >= (1/6) n^2 log(n).
```

It also proves the failure of an eventual `O(n^2)` bound for every `k >= 3`.
The endpoint in `Statement.lean` reproduces the exact definition and solved
lower-bound statement from the pinned Formal Conjectures source, and expands
the `answer(False)` assertion to its literal logical meaning.

## Contribution and prior work

The mathematics is credited to Wouter van Doorn and Terence Tao. An earlier
Lean development by Aristotle and Boris Alexeev already formalized this Pell
construction, a bound with factor `5^t`, and a negation of a global quadratic
bound using a maximum-powerful-divisor definition. That development was
inspected and is explicitly acknowledged; its proof scripts are not imported
or redistributed here.

This newly written implementation supplies an explicit `1/6` logarithmic bound,
unbounded witnesses, the exact prime-factorization definition, all `k >= 3`,
and the eventual Big-O endpoint. It uses a short ring-theoretic fifth-power
lifting identity and an elementary exponential growth estimate. Assessing
whether this increment merits formalization-contribution recognition is for
the organizers. See `PROVENANCE.md` for immutable sources and scope comparison.

Prepared with OpenAI ChatGPT assistance for the submitting account. Proposed
formalizer: `RECIPIENT-JSP-000303-KZ-A`, confirmation pending. This is a
self-submission, not an independent human verification attestation.

## Reproduce

Lean: `leanprover/lean4:v4.34.0`. Mathlib:
`5ed2965256430c3649e86755f9576b54eca72435` (v4.34.0).
All transitive revisions are locked in `lake-manifest.json`.

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first script builds with warnings as errors, replays both modules with
the bundled Lean kernel checker, audits eleven theorem dependency closures,
and rejects a false arithmetic control. The second builds commit-pinned
lean4export and independently implemented NaNoda, enforcing an explicit
allowlist of `propext`, `Classical.choice`, and `Quot.sound`.

The workflow in `workflow/jsp-000303.yml` performs these checks on Ubuntu.
Proof checking uses cached upstream dependencies; a full offline dependency
rebuild and official designated verification are not claimed. Actual run
results and archive receipts are supplied separately after execution.

Source is Apache-2.0; the copied statement retains the Formal Conjectures notice.

## Mathematical argument

Write `(3 + sqrt(8))^j = X_j + Y_j sqrt(8)`. The natural recurrence proves
`X_j^2 = 8Y_j^2 + 1`. Put `j_0=1`, `j_(t+1)=5j_t+2`, and
`n_t=8Y_(j_t)^2`; thus `2j_t+1=3*5^t`.

Both `n_t` and `n_t+1` are powerful. In the quadratic integer ring,
`(3+sqrt(8))^(3*5^t)` is congruent to `-1` modulo `5^(t+1)`.
The fifth-power lifting identity proves this by induction. Taking real and
irrational coefficients shows that `5^(t+1)` divides `n_t+2`. For `t>=1`,
this is a powerful prime power, so the triple product is at least
`n_t(n_t+1)5^(t+1)`.

The recurrence also gives `X_j+Y_j <= 11^j`. Hence
`log(n_t) <= 7+20j_t <= 6*5^(t+1)`, proving the constant `1/6`.
Strict growth of `Y_j` gives `n_t>t`, so the result holds arbitrarily far out.
Every additional powerful part is at least one, giving all `k>=3`.

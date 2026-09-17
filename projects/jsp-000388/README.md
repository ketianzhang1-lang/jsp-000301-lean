# JSP-000388 / Erdos 477: the divisible-coefficient quadratic obstruction

This project formalizes the known negative result for every integer polynomial
`f(x) = a*x^2 + b*x + c` with `a != 0` and `a` dividing `b`, including `b = 0`
and both signs of `a`. No set `A` of integers gives every integer exactly one
representation as `u + v`, with `u` in `A` and `v` in the value set of `f`.
Uniqueness is of value pairs, not polynomial inputs.

**Partial scope relative to JSP-000388.** The original question asks whether
ANY polynomial of degree at least two has such a complement. Its known answer
is yes, using even powers of degree at least six. This project does not prove
that positive result, make a new mathematical discovery, or settle the cubic
case. It formalizes a complete parameter family of the known quadratic
obstruction. Prize contribution eligibility requires organizer assessment.

## Mathematical argument

Write `b = a*d` and `q(x) = x^2 + d*x`. Every multiple of four is a
difference of two `q`-values. If `d = 2*e`, use inputs `t+1-e` and `t-1-e`;
if `d = 2*e+1`, use `2*t-e` and `2*t-e-1`. In either case the difference is
`4*t`. Therefore every multiple of `4*a` is a difference of two `f`-values.

If two elements of a purported exact complement have the same residue modulo
`4*a`, the corresponding difference of polynomial values yields two equal
sums. Uniqueness forces the two complement elements to coincide. The complement
is thus finite (indeed at most `4*abs(a)` elements, though that numerical bound
is not a separate checked theorem here).

The inequality `q(x) >= -d^2` implies the polynomial range is bounded below
when `a > 0` and above when `a < 0`. Adding a finite set preserves the relevant
bound, so the sum cannot cover all integers. This is the contradiction.

## Statements and verification

The main function-level theorem is `no_divisible_quadratic_complement`.
`polynomial_quadratic_obstruction` supplies the equivalent Mathlib polynomial
evaluation statement. `no_square_complement` covers the classical square case.
All are in namespace `JSP000388`.

The submitted source must be pinned to the commit actually verified. Before a
passing run is recorded, this is a development project, not verified evidence.
Reproduction uses Lean 4.34.0 and the committed Mathlib dependency manifest:

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

See `PROVENANCE.md` for sources and credit. No award, priority, payment,
independent human certification, or official verification is asserted.

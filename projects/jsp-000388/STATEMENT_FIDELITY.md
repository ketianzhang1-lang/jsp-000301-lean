# Statement correspondence (contributor review)

This is a scope comparison by the contributor, not a curator signature or an
independent human review.

## Original scope and the part covered

JSP-000388 corresponds to Erdos 477: does some integer polynomial of degree at
least two have an integer value set that tiles all integers by translation,
with a unique pair of summand values? The known answer is positive for certain
higher even powers. The present submission proves only the known negative
quadratic family. It must not be recorded as a proof of the general positive
existence theorem.

The reference statement is pinned at:
https://github.com/google-deepmind/formal-conjectures/blob/cd0084c96ac8764cac2c4dcb1b6f1815112f1155/FormalConjectures/ErdosProblems/477.lean

Its `degree_two_dvd_condition_b_ne_zero` variant assumes `a != 0`, `b != 0`
and `a | b`; its `S_sq` variant treats squares. Our theorem permits `b=0`
as well, and includes every translation `c` and either sign of `a`.

## Definitions

| Mathematical item | Formal expression |
| --- | --- |
| Arbitrary set of integers | `A : Set Int` |
| Actual polynomial values at integer inputs | `Set.range f` |
| A representation | `p.1 in A`, `p.2 in Set.range f`, `p.1+p.2=z` |
| Unique pair of values | `ExistsUnique` over `Int × Int` |
| Coverage of every integer | `forall z : Int` |
| Nonzero leading coefficient | `a != 0` |
| Divisibility restriction | `a` divides `b` |

The formulation does not require unique polynomial inputs: for example the
equal square values of `x` and `-x` count as the same second summand. The proof
of `left_unique` deliberately extracts only equality of the first summands.

`no_divisible_quadratic_complement` is the main function-level theorem.
`polynomial_quadratic_obstruction` uses Mathlib `Polynomial.C`, `Polynomial.X`,
and `Polynomial.eval`, and proves the equivalent failure of unique coverage at
some integer. The sum equality is written in the same orientation as the
reference statement. The use of `C a * X^2` is the standard coefficient form of
`a` acting on `X^2`; no custom polynomial evaluation is assumed.

## Mathematical dependency check

The proof constructs polynomial-value differences for every integer multiple
of `4*a`. Equal residues of complement elements then force equal elements,
which embeds the complement into a finite residue interval. A completed-square
inequality bounds the quadratic range on one side, for either sign of `a`.
This contradicts coverage of every integer after addition of a finite set.

There are no computational cutoffs, bounded coefficient searches, conjectural
analytic inputs, assumptions of the desired conclusion, or external unproved
lemmas. All arithmetic identities and the arbitrary-set argument are proof
obligations in the included Lean source. The numerical bound `4*abs(a)` stated
in the informal exposition is not a separate exported Lean theorem.

## Matters left to reviewers

Confirm this partial-family formalization is an eligible incremental
contribution; assess historical attribution and overlap with prior public
formal work. This project claims no global first priority, independent review,
or completion of the higher-degree existence question.

# Statement correspondence — JSP-000388 / Erdős 477

The existing prize catalog asks whether the integer value set of a polynomial
can have an additive complement with exactly one representation of each integer.
The original question requires an integer polynomial of degree at least two.

The formal statement reference inspected here is
[Formal Conjectures, pinned revision cd0084c96ac8764cac2c4dcb1b6f1815112f1155](https://github.com/google-deepmind/formal-conjectures/blob/cd0084c96ac8764cac2c4dcb1b6f1815112f1155/FormalConjectures/ErdosProblems/477.lean).
We use it as a statement reference; we do not import its unproved placeholders.

Our `JSP000388.jsp_000388` has the same existential integer polynomial,
`2 ≤ f.degree`, unrestricted integer complement set and unique ordered pair
of summand values in `A ×ˢ Set.range f.eval`. It differs only by omitting the
specification file's answer macro wrapper and directly proving the affirmative
proposition. The witness is the actual polynomial `Polynomial.X^6`.

The imported sixth-power theorem is unconditional: its full proof chain
establishes the finite-avoidance and counting prerequisites. Our equivalence
lemma relates its `IsTiling` predicate definitionally to `ExactComplement`.
No existence or asymptotic hypothesis is left as an input to the final theorem.

The preserved original module covers the negative square case and the
quadratic family `a*x²+b*x+c` with a≠0 and a dividing b. Our new translation
law and shifted-sixth-power consequences are additional results.
The main original question does not require a classification of all polynomials,
a decision for the cubic variant, or all even-exponent variants; none is claimed.

This development combines credited upstream mathematics and formalization with
our explicit additional contributions. Statement coverage is not a determination
of originality, prize priority, maintainer acceptance or award eligibility.

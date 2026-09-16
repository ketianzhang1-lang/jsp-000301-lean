# Attribution, prior formalization, and scope

This formalization implements a known mathematical construction. Anatoly S. Izotov,
A Note on Sierpinski Numbers, Fibonacci Quarterly 33(3) (1995), 206-207, supplies the
partial-cover plus algebraic-factorization method. Michael Filaseta, Carrie Finch,
and Mark Kozek, On powers associated with Sierpinski numbers, Riesel numbers and
Polignac's conjecture, Journal of Number Theory 128 (2008), 1916-1940, Section 2,
supply the explicit progression used here. The author-hosted preprint presents it
on printed page 6. Their mathematical credit is not claimed by this submission.

Important prior Lean work: HowieHwong/lean-erdos-proofs at
b8b641ba2d00dc4d1fe205a078a4159372672459, Erdos/P1113.lean, already proves the
unrestricted infinitude of Sierpinski numbers via Selfridge's 78557 progression.
The Formal Conjectures 1113 file links that proof. Our target is the different
explicit fourth-power family and its partial-cover/algebraic proof. We do not
claim to be first to formalize the unrestricted infinitude theorem, and do not
import or redistribute the prior proof. It was inspected for scope, not rebuilt.

Prior proof:
https://github.com/HowieHwong/lean-erdos-proofs/blob/b8b641ba2d00dc4d1fe205a078a4159372672459/Erdos/P1113.lean
Original problem and formal statement:
https://www.erdosproblems.com/1113
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1113.lean

The original open question asks for a Sierpinski number with NO finite covering
set of primes. This package does not answer it. Proving failure of one specified
seven-prime list does not prove failure of all finite lists. The general FFK
simultaneous-powers theorem for arbitrary R is also outside this package's scope.

The submitting account directed this independently written Lean development with
OpenAI ChatGPT assistance. Mathlib results and foundational infrastructure remain
credited to their contributors. Build caches and independently implemented
checkers run by the submitter are not independent human or organizer review.
No global priority, award, payment entitlement, or confirmed recipient is asserted.

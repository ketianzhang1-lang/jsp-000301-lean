# Statement and proof

For a set `B` of natural numbers, define

\[
D_0(B)\iff\lim_{n\to\infty}\frac{|B\cap[0,n)|}{n}=0.
\]

Define

\[
E=\{n\in\mathbb N:n\text{ is odd and there are no }k,p\in\mathbb N
\text{ with }p\text{ prime and }n=2^k+p\}.
\]

The final theorem is

\[
\neg\exists A,B\subseteq\mathbb N:\quad
E=A\cup B,\quad D_0(B),\quad
A=\{a+md:m\in\mathbb N\}\text{ for some }a\in\mathbb N,d>0.
\]

The theorem quantifies over all starts and all positive differences. Exponent zero is included. Zero itself is not an exceptional integer because it is not odd. No density-existence assumption is imposed on `E`.

## New bridge argument

If `S` contains every term `mk+a`, inject the indices `k<n` into `S cap [0,mn+a)`. This gives `count(S,mn+a) >= n`. For `n >= a` and `m >= 1`, we have `mn+a <= 2mn`, so the counting ratio at those cutoffs is at least `1/(2m)`. It cannot tend to zero. The Lean proof chooses an explicit large index after the convergence threshold.

Adding one point `b` to a set with no infinite arithmetic progression cannot create such a progression: if the union contained `mk+a`, the tail starting at index `b+1` would lie strictly beyond `b`, hence wholly in the old set.

Write `U` for the positive-exponent exceptional set used by the pinned prerequisite. The only odd integer representable using exponent zero but not a positive exponent is 3: a representation is `n=p+1`; oddness forces the prime `p` to be 2. Also 3 cannot be a prime plus a positive power of two. Thus `U = E union {3}` exactly.

A supposed decomposition `E=A union B` with `D_0(B)` gives `U=A union (B union {3})`. The two bridge lemmas show the second set has no infinite progression, contradicting the upstream negative-decomposition theorem. The positive-exponent version follows directly from the density implication.

## Existing mathematical and formal proof

The prerequisite establishes Chen's one-progression result using two explicit progressions of exceptional integers and a divisibility contradiction. Its mathematical and formalization credits remain with the original contributors. We do not claim these progressions, the number-theoretic argument, or the upstream proof as new work.

## Alignment and limits

`Erdos16Reference.erdos_16` has the definition shape of the published Formal Conjectures statement and is proved directly by `Erdos16Density.no_decomposition`. Its typechecking verifies definitional agreement, including the actual limit and exponent zero.

This statement alignment is an authored reference check, not an organizer-issued challenge or a proof of its own informal interpretation. No global priority claim is made. The source search is not exhaustive. The package contains no formalization of the stronger finite-union question.

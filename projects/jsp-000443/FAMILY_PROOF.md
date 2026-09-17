# Finite-field extension: proof and exact scope

For a finite field F of order q, the new Lean module `PolarityFamily.lean`
proves `q² + q + 1 ≤ R(C₄,K₁,q²)`. For even q, the previously proved
upper bound makes this an equality. Mathlib's `GaloisField 2 r` provides
a field of order 2^r for every positive r, so the result covers infinitely
many star sizes, with no bound on the exponent.

## Construction

Use the disjoint union of F × F and F as the vertex set: q² + q vertices.
Call the first kind affine vertices and the second kind direction vertices.
Distinct affine vertices (a,b), (c,d) are adjacent when b+d=ac.
An affine vertex (a,b) is adjacent to direction c exactly when a=c.
There are no edges between direction vertices and no loops.

For an affine vertex (a,b), each t in F gives the potential neighbor
(t,at−b). If that vertex equals (a,b), replace it with direction a.
This rule is injective and always gives an actual neighbor. A direction
vertex a has the q distinct neighbors (a,t). Thus every degree is at least q.

Two distinct affine vertices with the same first coordinate have no common
affine neighbor and at most one common direction neighbor. For different
first coordinates a,c, two common affine neighbors with first coordinates
s,z would imply (a−c)(s−z)=0; hence s=z, and the second coordinates agree.
A common direction neighbor would force a=c. For an affine vertex and a
direction vertex, the direction fixes the first coordinate of a common
neighbor, and the affine incidence equation fixes the second coordinate.
Two different directions have no common neighbor. Therefore distinct
vertices have at most one common neighbor, excluding every four-cycle.

The complement has degree at most (q²+q)−1−q=q²−1, so it contains no star
with q² leaves. This proves the lower bound. The upper bound for positive
even q comes from two-step-neighborhood counting and the degree-sum parity
argument in `JSP000443.lean`.

## Formal endpoints

- `JSP000443.PolarityFamily.lower_bound`: arbitrary finite fields.
- `JSP000443.PolarityFamily.exact_even`: finite fields of even order.
- `JSP000443.c4StarRamsey_power_two`: every positive exponent r.
- `JSP000443.c4StarRamsey_sixty_four`: R(C₄,K₁,64)=73.
- `JSP000443.c4StarRamsey_256`: R(C₄,K₁,256)=273.

The graph is transferred bijectively to the `Fin N` vertex convention of
`RamseyBound`. The existing graph-copy equivalences give ordinary,
non-induced copies of the four-cycle and the n-leaf star.

## Attribution and limitation

This is an independently written Lean formalization of classical
finite-field/polarity constructions and their known Ramsey consequence;
it does not claim a new mathematical theorem or first formalization.
See the Parsons reference and other background references in README.md.
The source was prepared with OpenAI ChatGPT assistance under the
submitting account's direction. No third-party solution file was copied.

This does not determine all star Ramsey numbers, establish the original
unbounded-deficit conjecture, or establish eligibility for an award.
The verification record distinguishes this extension from the previously
checked, single-parameter certificate.

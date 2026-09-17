# Statement fidelity

Final theorem: `JSP000617.upper_density_variant`.

- ε is any positive real number.
- A is a genuine `Set ℕ`, constructed as the union of increasing finite stages.
- `sumset A` is exactly `{n | ∃ a∈A, ∃ b∈A, a+b=n}`.
- `orderedRep A n` is the cardinality of the pairs in `Finset.antidiagonal n`
  whose two coordinates belong to A. It counts both orders and includes diagonal
  pairs. This is the same ordinary two-term representation function as the
  self-convolution of A's indicator function.
- `prefixSet S N` filters `Finset.range N` by membership in S. Thus it is exactly
  S∩[0,N), with cardinality ≤N.
- `upperDensity S` is the limsup, as N tends to infinity, of that cardinality
  divided by N in ℝ. Division at N=0 follows Lean's convention and has no effect
  on the limsup.
- The single natural constant C is quantified before n and works for every n.
  No block-size-dependent bound or unproved hypothesis appears in the result.

The finite `ZMod p × ZMod p` model is only an intermediate construction. The
completed target uses ordinary addition on ℕ and the actual infinite union.
`infinite_representations` proves the uniform bound on that union;
`infinite_dense_prefixes` proves good prefixes beyond every threshold;
`fixed_upper_density` converts these witnesses to the standard limsup inequality.

The original Erdős #749 statement in Formal Conjectures uses lower density and
remains distinct. This project neither redefines lower density nor replaces it
inside the original statement, and makes no claim of solving that original problem.

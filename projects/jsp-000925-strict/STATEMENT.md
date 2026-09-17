# Statement fidelity

The number N is the number of derivative roots; f has degree N+1 and N+1
arithmetic-progression roots. This avoids the inconsistent degree/root indexing
noted in the prior evidence registration.

`JSP000925Strict.strict_gap_theorem` assumes the listed derivative zeros are in
the corresponding open intervals and proves `RightGapStrict N b` and
`Erdos1114.GapSymmetric N b`.

`JSP000925Strict.exists_unique_strict_gaps` removes the assumed selector. Its
hypotheses are only N>0, d>0, f nonzero, natDegree f=N+1, and vanishing at
all N+1 progression points. It returns b, interval membership, derivative zero,
uniqueness within each interval, strict outward right-hand gaps, and reflection
symmetry. By reflection, the left-hand gaps strictly decrease when read left to
right toward the center.

The precise strict comparison is
`i+2<N -> N<=2*(i+1) -> b(i+1)-b(i)<b(i+2)-b(i+1)`.
For odd N the two mirror-image central gaps are equal; the comparison excludes
that pair. For even N the single central gap is compared with its right neighbor.
No numerical tolerance, finite-degree cutoff, zero-polynomial case, or positive
leading-coefficient assumption is introduced. No assertion about unequally spaced
roots, higher derivatives or Lorch's separate degree-variation results is made.

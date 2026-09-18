# Prior art and scope of incremental work

Checked on September 17, 2026. These are scoped searches, not a proof of priority.

- Heckel's 2024 Proposition 3 is the mathematical source for this package:
  https://doi.org/10.37236/13346 and https://arxiv.org/abs/2408.13839.
- Mathlib's Harris-Kleitman development is imported without changes, at
  `5ed2965256430c3649e86755f9576b54eca72435`:
  https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Combinatorics/SetFamily/HarrisKleitman.lean.
- A separate, existing formalization of the stronger asymptotic resolution is
  publicly reported in SamPetkov/Erdos. Its README at the checked revision
  explicitly claims a complete result, with 480 local modules and a different
  quantitative target:
  https://github.com/SamPetkov/Erdos/blob/b3fdc4d3efbe6c999faac3da4614cc3036b3b3ea/625/formalization/README.md.
  That work was located during the final overlap search, after this package's
  code was first written and pushed. No source from it was imported or copied.
  Its existence rules out representing this package as the first Lean work on
  Erdős 625. Its build and complete dependency closure were not audited here.
- The file at
  https://github.com/daedalus/alphaproof-nexus/blob/4e65a6ca81655f090a3c8dcf9f56e4a38c984f4c/problems/erdos/625/Erdos625.lean
  contains a problem description and an empty development block at that revision.
- Queries for `JSP-000506` in the prize issue/PR records returned no matches.
  Searches for `Heckel` with `Harris`, and for `0.999`, in SamPetkov/Erdos
  returned no indexed matches. Search absence does not establish novelty.

The requested review concerns only this independently written formalization
of the finite concentration reduction and its explicit graph specialization.
The original mathematical result and the stronger existing formalization remain
credited to their published authors. No full-problem, first-priority, or automatic
reward claim is made. The organizers must assess whether this incremental work
is eligible at all.

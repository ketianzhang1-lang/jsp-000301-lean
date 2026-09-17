# Catlin graph: exact chromatic and subdivision numbers

For the explicit 15-vertex graph C5[K3], `CatlinComplete.sharp_catlin_counterexample`
proves that the Mathlib chromatic number is 8 and that a K_r subdivision exists
if and only if r <= 7, for every natural r.

The subdivision model uses actual simple graph paths for all branch pairs,
requires their interiors to be pairwise disjoint, and excludes every branch
vertex from every interior. No graph-theoretic conclusion is assumed.

- [SHARP_PROOF.md](SHARP_PROOF.md): new K7 witness and the exact classification.
- [PROOF.md](PROOF.md): the existing colouring and K8 obstruction arguments.
- [PROVENANCE.md](PROVENANCE.md): original code lineage and attribution.
- [RECEIPT.md](RECEIPT.md): successful cloud check, immutable source and artifact hashes.
- [SUBMISSION.md](SUBMISSION.md): complete scoped contribution review request.
- [VERIFICATION.md](VERIFICATION.md): executed checks and reproduction instructions.

The mathematical counterexample is classical and credited to Catlin. This
formalization and its supplement were prepared with OpenAI ChatGPT assistance.
The new supplement adds the attainable lower boundary and restriction theorem;
no novelty or first-formalization priority is claimed.

This is a scoped finite contribution related to JSP-000585 / Erdos 717, not a
solution of its asymptotic bound for arbitrary finite graphs. Eligibility and
any reward require organizer assessment.

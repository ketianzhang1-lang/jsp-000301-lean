# JSP-000057: the sharp rank-two, three-petal sunflower threshold

This project proves **`Erdos20.f 2 3 = 7`** in Lean 4.34.0, with the set-family
threshold definition used by Formal Conjectures. It formalizes a classical
elementary special case of JSP-000057 / Erdős problem 20. **It does not prove
the general sunflower conjecture, improve a known mathematical bound, or
claim a first formalization.** Award eligibility is for the organizer to assess.

## Mathematical argument

View distinct two-element sets as edges of a simple graph. If an element
belongs to at least three edges, those three edges have pairwise intersection
exactly that singleton. Otherwise every vertex has degree at most two.
Selecting an edge removes at most three edges that meet it (including itself).
Starting with at least seven edges, three successive choices therefore produce
three pairwise disjoint edges, a sunflower with empty kernel.

The six edges of two disjoint triangles contain neither three edges with a
common vertex nor three disjoint edges. The finite counterexample is checked
by Lean's kernel-reduced `decide`; `native_decide` is not used.
Thus seven is sufficient and six is insufficient.

## Checked statements

- `seven_forces_three`: upper bound for finite families over any ground type.
- `twoTriangles_no_three`: the explicit six-member lower-bound witness.
- `threshold_iff`: the finite-family threshold predicate holds exactly for `m >= 7`.
- `seven_forces_three_sets` and `twoTriangles_sets_no_three`: transfer to
  the original `Set (Set α)` formulation.
- `original_threshold_iff`: the exact predicate defining `Erdos20.f` holds
  exactly for `m >= 7`, so the infimum is nonempty and sharp.
- `f_two_three`: `Erdos20.f 2 3 = 7` without added mathematical hypotheses.

See [statement alignment](STATEMENT.md) and [source attribution](PROVENANCE.md).

## Reproduce

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

`lean-toolchain` pins Lean and `lake-manifest.json` locks all dependency
revisions. The first script builds with warnings treated as errors, replays
the module with `leanchecker`, checks eight theorem axiom closures against
`propext`, `Classical.choice`, and `Quot.sound`, verifies actual dependency
revisions, and checks that a false arithmetic statement is rejected.
The second exports the eight theorem dependency closures with a pinned
`lean4export` and checks them with pinned NaNoda using a strict axiom allowlist.
GitHub Actions archives tested source, statements, and verification evidence
for 90 days. A successful contributor run is not organizer verification.

## Contribution scope

Prepared for Ketian Zhang with OpenAI ChatGPT / Codex assistance. The
contribution is this independently written Lean proof, sharp lower/upper
bound integration, original-definition bridge, and reproducible evidence.
The general conjecture remains unresolved. No change to the full problem's
catalog eligibility or solution status is requested by this scoped project.
License: [Apache-2.0](LICENSE-APACHE-2.0); see [NOTICE](NOTICE).

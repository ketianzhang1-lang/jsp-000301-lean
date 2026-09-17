# JSP-000392: Schur lower bounds from Exoo's 160-element coloring

This is a formalization contribution for review, not a solution of the open
asymptotic Schur-number problem and not an award announcement.

For every natural r, the proof constructs a coloring of
`{1,...,(321*3^r-1)/2}` with at most `5+r` colors and no monochromatic solution
of `x+y=z`. Equal summands are allowed. It also constructs a symmetric edge
coloring of the complete graph on one more vertex with no monochromatic
triangle. In standard notation the resulting bounds are

- `S(5+r) >= (321*3^r-1)/2`;
- `R_{5+r}(3) >= (321*3^r-1)/2 + 2`.

If f(k) denotes the first interval size forcing a monochromatic sum, it is
S(k)+1. `exoo_forcing_lower` explicitly proves failure of forcing at the
constructed length. We do not prove the optimality S(5)=160, a new numerical
record, or the optimal exponential growth rate.

The seed is Exoo's published symmetric five-color partition of [1,160]. Its
finite certificate is evaluated by Lean's kernel (`decide +kernel`). A symbolic
reflection proof extends every k-coloring of [1,N] to a (k+1)-coloring of
[1,3N+1]. Induction proves the complete parameter family. The triangle result
uses the color of the absolute difference between two vertices.

## Reproduce

Pinned Lean: 4.34.0. Pinned Mathlib and all transitive dependencies are recorded
in lake-manifest.json. With elan installed:

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The first script builds with warnings treated as errors, replays the bundled
kernel, audits twelve theorem dependency closures, checks actual dependency
revisions, and rejects a false arithmetic control. The second exports those
closures and checks them with an independently implemented checker, NaNoda,
permitting only propext, Classical.choice and Quot.sound.

These are contributor-run checks. No independent human or organizer review,
priority determination, minimum-safe-version decision, or prize eligibility
is claimed. The workflow uses network access and precompiled Mathlib caches.
See PROVENANCE.md for mathematical credit and overlap checks.

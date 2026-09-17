# Catlin graph research checkpoint — not a prize submission

A complete human-readable proof of the known Catlin counterexample and
finite Lean certificate components. See PROOF.md for attribution and exact
scope. This does not complete JSP-000585 / Erdos 717.

Files:
- PROOF.md: graph construction, colouring proof, and path-counting obstruction.
- Certificate.lean: six finite/arithmetic theorem components; no path bridge.
- verify.py: independent exact enumeration, with no third-party dependencies.
- all_155_branch_profiles.csv: every feasible branch-count profile (generated).
- python_verification.json: actual Python output (generated).
- lean-verification.log: available in CI artifacts after an actual CI run.

No upstream prize application is made by this checkpoint. Any future
application must accurately distinguish the original asymptotic problem from
the Catlin counterexample and must complete the claimed formalization.

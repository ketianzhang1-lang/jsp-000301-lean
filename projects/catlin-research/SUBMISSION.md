# [Recipient] JSP-000585: verified exact Catlin subdivision threshold (scoped)

### Related problem or entry

JSP-000585 / Erdos 717 — related finite Catlin counterexample; scoped formalization.

### Recipient placeholder or confirmed public ID

RECIPIENT-JSP-000585-CATLIN-KZ-A

### Contributions and evidence

Please assess this formalization contribution and whether a scoped-contribution recognition pathway applies. For the explicit 15-vertex graph C5[K3], the theorem proves chromatic number 8 and, for every natural r, existence of a K_r subdivision if and only if r <= 7.

The new supplement constructs all 21 K7 paths, proves a branch-set restriction theorem, and completes the exact subdivision-order classification. It extends the account's earlier colouring and no-K8 proof; the final model uses actual Mathlib simple paths with pairwise disjoint interiors avoiding every branch vertex. A clean-build module-registration defect was also repaired.

Pinned source, proof explanations and attribution:
https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/019467ead20f2d6b87e672a1dfef7d5b8886febf/projects/catlin-research

Verification: clean build, seven module replays, twelve axiom audits, a rejected false-arithmetic control, and NaNoda's 7,621-declaration check all passed at the pinned commit.

Verification run:
https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176307046

This is not a proof of the uniform asymptotic inequality for arbitrary graphs in the original JSP-000585 question, and no change to the catalog's solved/Lean/eligibility flags is requested.

### Confirmation status

Pending. No public attestation of written recipient confirmation is supplied.

### Attribution questions and conflicts

Self-submission prepared with OpenAI ChatGPT assistance. The mathematical counterexample is classical and credited to Catlin; see Fox, Lee and Sudakov, https://arxiv.org/abs/1107.1920 . Original module lineage and the existing external Erdos 717 formalization are disclosed in PROVENANCE.md. No new-mathematics claim, first-formalization priority, independent human sign-off, organizer approval or payment entitlement is asserted. Please review scope and overlap before allocating any credit or award.

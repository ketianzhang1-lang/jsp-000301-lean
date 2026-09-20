# JSP-000393: sparse polynomial squares over characteristic-zero fields

Selected proof commit: `aa1ed1bac2eb0c1ec33723ff802ff3b9b6c02ee8`, branch `jsp-000393-general-coefficients`. Executed verification results belong to the separately dated report for this exact commit.

This completion corrects a coefficient-domain limitation in the earlier rational-only package. The original historical conjecture is stated for **complex coefficients**, as Schinzel (1987), printed p.55, makes explicit. The new `JSP000393General.lean` proves the support bound, the divergence of the actual minimum, exact sparse-family counts, and arbitrarily large small-ratio witnesses over every characteristic-zero field, including the complex numbers.

- Main declaration: `JSP000393General.jsp_000393` (arbitrary characteristic-zero field).
- Literal original-domain endpoint: `JSP000393General.complex_original`.
- Original sources, statement mapping, and proof route: [GENERAL_COEFFICIENTS.md](GENERAL_COEFFICIENTS.md).
- Attribution: [PROVENANCE.md](PROVENANCE.md).
- Complete original construction/rational integration are unchanged from the earlier proof version `17e406594d644b40c9a742e843cd6d89f319c872`. That old commit does not contain the new coefficient-domain extension.

Use the exact new proof commit identified in the submission; do not replace it with a later branch tip. From that checkout, in an isolated environment with the pinned Lean 4.34.0 toolchain:

```bash
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
python3 scripts/verify_general.py
lake env lean -DwarningAsError=true AuditGeneral.lean
```

The verifier freshly compiles all 22 pinned upstream modules, the two earlier local proof modules, their audit entry, the new general-field module, and its audit entry (27 modules). It audits the original 13 theorem closures and the 11 new ones, checks all nine dependency revisions, invokes kernel replay, and rejects false arithmetic. The separately supplied `lean-verify` report records the actual semantic-bridge, target, kernel and external-checker results with their checked commit, execution date and logs. These reproduction instructions are not themselves a verification verdict.

No mathematical discovery, independent reproof of the upstream algebraic reduction, exclusive authorship, or award eligibility is claimed. The prior rational-only record, earlier verification receipts, and original contribution remain identifiable in Git history.

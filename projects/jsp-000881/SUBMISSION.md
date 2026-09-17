### Related problem or entry

JSP-000881 / Erdos Problem 1061:
https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000881

### Recipient placeholder or confirmed public ID

RECIPIENT-JSP-000881-KZ-A. Public identity confirmation is pending.

### Contributions and evidence

Please assess a **partial formalization contribution**, not a solution of the open conjecture.

For the original ordered count S(x) of positive pairs (a,b) with a+b <= x and
sigma(a)+sigma(b)=sigma(a+b), the new Lean package proves

    S(x) >= (38/135)*x - 76, for every real x >= 0.

It also proves S(N) >= 76*floor(N/270), the corresponding epsilon lower
asymptotic statement, and infinitude. The proof gives coprime multiples of
(1,2) and (4,5), counts both orientations, proves distinctness, and formally
connects the integer count with the original real-argument definition.

Pinned source, definitions, scope, attribution and reproduction instructions:
https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/bad12390f362ae74b0c825256824b9fdaf897136/projects/jsp-000881

Dedicated verification run:
https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176439458

The run completed successfully: standard Lean build, two kernel replays, ten
target axiom audits, pinned dependency checks, negative control and independent
NaNoda verification of 9,711 declarations. Only the three standard axioms were
permitted. These applicant-run checks are not organizer acceptance. The source
commit and run must be reviewed together.

The original conjecture S(x) ~ c*x remains open: this package proves no limit,
matching upper bound or value of c. The catalog currently says Eligible to
claim: No. Please assess whether this explicitly limited formalization merits
intake or recognition. No eligibility change or award announcement is proposed.

### Confirmation status

Pending organizer scope, attribution, overlap, verification and eligibility
review. No written recipient confirmation or designated-verifier statement is
supplied.

### Attribution questions and conflicts

Self-submission by the public account ketianzhang1-lang, prepared with OpenAI
ChatGPT assistance. The original problem and counting convention are credited
to the references and Formal Conjectures Authors documented in README.md;
Mathlib supplies the classical multiplicativity theorem. The elementary seeds
and lower-bound argument are not claimed as new mathematics or an improved
best-known bound. No global first-formalization priority, independent human
review, organizer approval, payment entitlement or curator/verifier role is
asserted. No corresponding JSP-000881 issue or PR was found in the repository
search at preparation time; that limited search is not a priority guarantee.

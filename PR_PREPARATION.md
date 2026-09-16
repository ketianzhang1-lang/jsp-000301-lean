# PR preparation notes — not a filed pull request

Suggested title: `JSP-000301: add formalization and reproducible verification evidence`

## Intended scope

Submit the Lean formal statement, proof and linked evidence for review, preserving the catalog's existing mathematical credit and all earlier formalization submissions. Do not mark the submission as officially verified, announced, paid or first in priority.

Verified proof snapshot: `e1a17b0d6728b9d4929d1d4abd3721a27377369a`.

CI evidence: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35131699133

## Outstanding steps

1. The repository owner creates a fork of `TheJustinSunPrize/awards` in GitHub. The currently exposed integration cannot create forks and rejected a direct official-issue write with HTTP 403.
2. Read the current official record templates and schemas, then prepare a dedicated branch in that fork. If a candidate record is used, maintain pending-review/pending-confirmation fields and never invent public reviewer signatures. Include the formal statement, proof source and evidence pointers.
3. Run the official repository validation, link, generation and test commands before publishing the record changes. These repository checks validate records, not the Lean proof.
4. Open the cross-fork PR against the designated official base repository. The final submission may need to be sent by the user in the GitHub web session if integration permissions still prevent it.

No official-schema candidate package or generated official data is represented as completed in this preparation folder. The proof/evidence files and recipient draft are ready; their insertion into an official record awaits the fork and current-schema validation.

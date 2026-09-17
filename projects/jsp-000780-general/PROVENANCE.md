# Provenance and overlap

Prepared 2026-09-17 by OpenAI ChatGPT assisting the account holder
`ketianzhang1-lang` (Ketian Zhang). This package was independently written
from the documented binomial construction and existing r=6 project.

The mathematical construction is credited to GPT-5.5 Pro prompted by
Liam Price in the pinned [Formal Conjectures source](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/939.lean).
It already describes splitting the j=3 coefficient to cover every r≥6.
The present explicit arithmetic progression makes a prime search unnecessary;
that observation and this implementation are not asserted to be novel.

A competing submission's [prior-art statement](https://github.com/inoader/awards/blob/b5b70857b2d77d6a060e00956beb8e19918b48f9/submissions/jsp-000780/PRIOR_ART.md)
reports Liam Price's 2026-05-24 playground link to an Aristotle proof,
with declarations `infinite_rpowerful_sums` and
`infinite_rpowerful_sum_tuples`, covering r≥6. The linked discussion could
not be retrieved directly in this session (HTTP 403); the report is not
presented as an independent replay of that prior proof. It is sufficient
reason not to claim first-formalization priority.

Existing [award PR #370](https://github.com/TheJustinSunPrize/awards/pull/370)
contains the account holder's r=6 specialization. This package supplements
its mathematical scope; it is not a separate discovery claim or separate
application for the same result. No change to author or recipient records
is proposed here. Its assessment must account for the prior general proof.

No result is claimed for the r=4 existence question, r=5 infinitude,
the noncube three-full triple variant, or the complete JSP-000780 problem.
No claim is made that an official catalogue label establishes eligibility,
that a CI check is organizer review, or that any prize has been awarded.

The predicate translation uses the prime-factor definition in
`FormalConjecturesForMathlib/Data/Nat/Full.lean`. The original problem's
`Finset.Coprime` means collective gcd 1. Reproduced statement content remains
attributed to the Formal Conjectures authors, under Apache-2.0. The new
implementation is distributed under Apache-2.0 as well.

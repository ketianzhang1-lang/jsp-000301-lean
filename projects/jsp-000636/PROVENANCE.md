# Our implementation, mathematical sources and prior submissions

We developed this implementation under GitHub account `ketianzhang1-lang`,
with OpenAI ChatGPT/Codex assistance. We retain the code license and Mathlib
attribution. We do not claim new mathematics or first-formalization priority.

## Our source history and current additions

The six-module pair-label development was published at
`d5fc3ee7fc5a452e8104b5099c854a5a15a668bf`. The ten-theorem asymptotic and
exact-multiplicity supplement was published at
`36da76e793678ee6a062f1703674fd3789334cbd`. Both are in branch
`jsp-000636-pair-label-upper-kz` of `ketianzhang1-lang/jsp-000301-lean`.

This revision preserves all seven proof modules from the latter commit byte
for byte. We add eight theorems in `OriginalQuestion.lean`: injective family
relabeling, invariance of cardinality/level counts/antichain/exact multiplicity,
finite-ground-set transfer, the explicit original existence/impossibility
statement and the combined complete threshold-estimate endpoint. We extend
the audits and reproduction scripts to cover 79 public theorems.

## Mathematical credit

Yixin He and Quanyu Tang retain credit for the lower-bound proof and label
construction method in arXiv:2602.09803v1. The original profile problem and
classical obstruction are attributed to Erdős and Trotter. Our pair-label
specialization and asymptotic consequences do not improve the source paper's
quantitative error term. No external non-Mathlib Lean proof is imported.

## Existing prize work

[PR #677](https://github.com/TheJustinSunPrize/awards/pull/677), by
`peilinliu66-dev`, predates the publication of our asymptotic supplement and
proposes a stronger exact threshold formula for all r≥2. Its selected source is
`peilinliu66-dev/jsp-000636-lean`, branch
`codex/jsp000636-kernel-certificate`, commit
`73d6fd31a21947fb538e9ace14c855c806802c6c`.
It credits mthiim and contributors for the reused r≥4 core and the applicant
for the small-parameter interfaces, integration and certificate replacement.
We inspected public statements and source inventory but did not independently
rebuild or certify that complete development. None of it is imported here.

We request assessment of our separately implemented proof and additional
interfaces in view of that work. A complete estimate endpoint is not a claim
to the stronger exact formula, earlier submission priority, organizer acceptance
or an award. The revised existing PR #382 proposes only catalog proof information
and attribution, with official eligibility and award decisions left to maintainers.

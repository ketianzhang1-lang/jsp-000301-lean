# Contribution and source record

We developed this implementation and the asymptotic supplement under GitHub
account `ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance. We use
Mathlib's standard infrastructure and retain the source license notices.

## Our code lineage

The parent proof revision is
`d5fc3ee7fc5a452e8104b5099c854a5a15a668bf`, branch
`jsp-000636-pair-label-upper-kz` of `ketianzhang1-lang/jsp-000301-lean`.
The six inherited proof modules and pinned dependency manifest are unchanged.
We add `Asymptotics.lean`, its ten theorems, expanded axiom audits, verification
coverage and scope documentation.

Our additions implement the exact-r maximum, its equality with the at-least-r
maximum, least-threshold correspondence, a quantitative relative-error bound,
the real asymptotic limit, and an exact-r extremal estimate endpoint.

## Mathematical credit

Yixin He and Quanyu Tang retain credit for the lower-bound proof and label
construction method in arXiv:2602.09803v1. The original profile question and
classical obstruction are attributed to Erdős and Trotter. Our pair-label
specialization and the asymptotic consequences do not constitute a claim of new
mathematics or of a better quantitative estimate than the source paper.

## Existing prize submission

[PR #677](https://github.com/TheJustinSunPrize/awards/pull/677), by
`peilinliu66-dev`, predates publication of this supplement and proposes a
stronger exact threshold formula for all r≥2. Its selected source is
`peilinliu66-dev/jsp-000636-lean`, branch
`codex/jsp000636-kernel-certificate`, commit
`73d6fd31a21947fb538e9ace14c855c806802c6c`.
It credits mthiim and contributors for the reused r≥4 core, and the applicant
for the small-parameter interfaces, integration and certificate replacement.
These authors' work is acknowledged, and is not imported by this package.
Inspection of public source and metadata is not an independent verification of
that complete development or a determination of award priority.

We request credit only for our concrete implementation and verified additions.
Maintainer acceptance, full-scope eligibility and any award decision remain
unconfirmed.

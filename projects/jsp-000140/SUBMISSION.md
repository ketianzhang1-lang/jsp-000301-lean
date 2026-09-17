# JSP-000140: strict 5/6 lower bound (partial scope)

## Related entry and contribution

JSP-000140 / Erdos 136. This is a self-submission of a separate Lean
implementation of the classical lower-bound component, with strictness and
integer rounding. For every n >= 4, a symmetric k-coloring of K_n in which
every four-element subset sees at least five colors satisfies

    5*(n-1) < 6*k,
    floor(5*(n-1)/6) + 1 <= k.

The package proves the counting argument for arbitrary n and k and proves the
bridge to the standard four-element-subset condition. It does not prove the
matching asymptotic upper bound or complete the catalog problem.

Proposed formalization recipient: `RECIPIENT-JSP-000140-KZ-A`, confirmation
pending. No mathematical solver nomination is made.

## Evidence

- [Pinned proof and exact scope](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/e3191a77503c145dde16a2b4e4a9489a92947812/projects/jsp-000140).
- [Dedicated verification run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178843250). See VERIFICATION.md for the actual
  outcome and completed stages; a run link alone is not a success assertion.
- Lean v4.34.0, Mathlib revision 5ed2965256430c3649e86755f9576b54eca72435.
- Local frontend, standard cloud build with warnings as errors, two kernel
  replays, ten axiom audits, locked dependency checks and the invalid-proof
  negative control passed. Only propext, Classical.choice and Quot.sound were
  reported. NaNoda checked 6,554 declarations with no errors.
- Workflow artifact ID 10479915118: 4,572,004 bytes; GitHub-reported ZIP digest
  sha256:3854184ba587692eeb85b38e73196d0605aa15b312719aa5518679c257429eb0.
  Retention and verification limits are disclosed in VERIFICATION.md.

## Attribution and existing formalization

The lower bound is due to the classical Erdos-Gyarfas argument, with earlier
attribution to Erdos, Elekes and Furedi as documented in Theorem 2 of
[Bennett et al. (2022)](https://arxiv.org/html/2207.02920v1).

The public [plby/lean-proofs entry](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos136.lean)
already declares a full formalization and includes a lower-bound module.
That work is disclosed rather than claimed as this account's contribution.
This submitted package imports only Mathlib, uses newly written proof code,
and claims neither new mathematics nor first-formalization priority.

Prepared with OpenAI ChatGPT assistance. The submitting account ran the checks
and has an interest in recognition; these are not organizer-run checks or
independent human review. Identity confirmation and any attribution review
remain pending. No private contact or payment information is included.

## Requested review

Please assess whether this independently written, scoped formalization is
appropriate for intake and any applicable contribution recognition, taking the
existing public formalization into account. The catalog marks Eligible to
claim: No. No award, eligibility change, priority decision, or payment
entitlement is asserted. No catalog, candidate or award record is changed.

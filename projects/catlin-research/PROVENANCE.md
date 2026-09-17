# Provenance and contribution scope

## Mathematical credit

The counterexample to Hajos's conjecture is classical and credited to Catlin.
The explicit graph is C5[K3]: five three-vertex cliques linked around a pentagon.
See Fox, Lee and Sudakov, [Chromatic number, clique subdivisions, and the
conjectures of Hajos and Erdos-Fajtlowicz](https://arxiv.org/abs/1107.1920),
which distinguishes Catlin's 1979 disproof from the later uniform asymptotic problem.
No mathematical discovery or worldwide first-formalization priority is claimed.

## Code lineage

All referenced commits below belong to the submitting account's
[jsp-000301-lean repository](https://github.com/ketianzhang1-lang/jsp-000301-lean).

| Revision | Contribution |
| --- | --- |
| `96ca7edd443f661da2b5763bc1a5834533968c21` | Earlier finite certificates in Certificate.lean |
| `fd8b01d24b01d313dbec6c09934d19f78feb001b` | Actual graph-path counting argument and chromatic-number proof in GraphCore, Profile, Subdivision, Colouring and Catlin |
| `9ce0e526bb4f81ce9d42436b851be10b376236a0` | Lake module-registration fix for clean builds; original proof then passed cloud verification |
| `019467ead20f2d6b87e672a1dfef7d5b8886febf` | Explicit K7 witness, branch-set restriction, and exact subdivision-order classification in Sharp.lean |

The formal work was prepared with OpenAI ChatGPT assistance under the submitting
account's direction. Mathlib supplies standard graph, path, colouring, finite-set
and arithmetic infrastructure. No imported research theorem assumes the Catlin
graph's no-K8 obstruction. The scripts use the account's pinned lean4export and
NaNoda checking workflow. The new supplement's proof uses ordinary kernel
reduction, not native_decide or an external search oracle.

## Existing external work and the original question

A public source for the distinct full asymptotic Erdos 717 theorem is
[Erdos717.lean in plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos717.lean).
Its stated informal authors are Fox, Lee and Sudakov; it credits Codex and
GPT-5.6 Sol for formal work. It is not imported by this package, and no independent
rebuild of that project is asserted here.

This finite Catlin result does not solve the original uniform asymptotic
JSP-000585 / Erdos 717 inequality for arbitrary graphs. Any recognition of this
scoped contribution must be assessed separately by the organizers. Reviewers
should examine overlapping implementations before allocating credit.

## Recipient and review record

The existing recommendation is [Issue #417](https://github.com/TheJustinSunPrize/awards/issues/417).
The proposed contributor remains `RECIPIENT-JSP-000585-CATLIN-KZ-A`, with written
confirmation pending. This is a self-submission with an interest in the outcome.
No independent human sign-off, organizer approval, award, or payment entitlement
is asserted. No private contact, identity document or payment information is supplied.

This provenance file is added by the PR because earlier public package documents
referenced PROVENANCE.md without including it in that source snapshot.

# Contribution review supplement: JSP-000636, 000912, 000393 and 000728

Prepared on 2026-09-19 for the existing Lean-only applications of
`ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance.
This supplement adds reproducible source-history evidence and a contribution map.
It does not replace or modify the selected Lean proofs.

| Problem | Existing catalog PR | Existing award claim | Proof branch | Selected proof commit |
| --- | --- | --- | --- | --- |
| JSP-000636 | [#382](https://github.com/TheJustinSunPrize/awards/pull/382) | [#1353](https://github.com/TheJustinSunPrize/awards/issues/1353) | `jsp-000636-pair-label-upper-kz` | `5c23ecf6211449c9bd7f4ac9229300ed43f666b2` |
| JSP-000912 | [#691](https://github.com/TheJustinSunPrize/awards/pull/691) | [#1351](https://github.com/TheJustinSunPrize/awards/issues/1351) | `jsp-000912-complete-proof` | `bf99214b3104d89c628abb9c824a56d89a6bd6fe` |
| JSP-000393 | [#368](https://github.com/TheJustinSunPrize/awards/pull/368) | [#1479](https://github.com/TheJustinSunPrize/awards/issues/1479) | `jsp-000393-sparse-squares` | `17e406594d644b40c9a742e843cd6d89f319c872` |
| JSP-000728 | [#373](https://github.com/TheJustinSunPrize/awards/pull/373) | [#1480](https://github.com/TheJustinSunPrize/awards/issues/1480) | `jsp-000728-lower-bound-kz` | `22212651d30af02ad36f01a206984d31b0ec75c6` |

All four proofs are in [the same multi-problem repository](https://github.com/ketianzhang1-lang/jsp-000301-lean).
The repository name refers to its original project; 636, 912 and 728 have
separate directories `projects/jsp-000636`, `projects/jsp-000912` and
`projects/jsp-000728`. The selected 393 project is at its branch's repository root.
Review the named branch and exact commit, not the default branch.

## JSP-000636

### Contribution and original statement

Our eight-module implementation connects the obstruction, pair-label construction,
exact-multiplicity thinning, least-threshold semantics and asymptotic estimates to
arbitrary finite ground types. The complete endpoint is
[JSP000636.jsp_000636](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5c23ecf6211449c9bd7f4ac9229300ed43f666b2/projects/jsp-000636/OriginalQuestion.lean).
Its `original_threshold_question` component covers every `r ≥ 2`:
for `n > 2*r + 4*Nat.sqrt r + 7`, an exact-multiplicity antichain of cardinality
`r*(n-3)` exists, and one of cardinality `r*(n-2)` does not.
The least-cutoff bounds for `r ≥ 4` and the limit `n₀(r)/r → 2` are separate,
explicit conclusions.

[He and Tang, arXiv:2602.09803v1](https://arxiv.org/html/2602.09803v1)
states the original request for threshold estimates in Problem 1.1, explains
exact versus at-least multiplicity in Remark 1.2, and defines the least cutoff
in Definition 1.3. Their paper supplies stronger quantitative estimates than
our implementation. This supports a catalog correction from Open to Solved
for the estimate question, with mathematical-solver credit to **Yixin He and
Quanyu Tang**, and a publication reference to that version. This is a proposed
mathematical-status correction for maintainer review, not a claim that the Lean
proof or applicant has been approved.

### New evidence

The verifier compares all seven preceding proof modules at
`36da76e793678ee6a062f1703674fd3789334cbd` with the selected proof:
`JSP000636`, `Construction`, `Lower`, `Thinning`, `Threshold`,
`Upper` and `Asymptotics`. **All seven are byte-identical.**
The selected version adds the eight theorems in `OriginalQuestion.lean`;
we do not backdate that addition to earlier partial submissions.
The direct imports in the eight proof modules are those local modules and Mathlib.

[PROVENANCE.md](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5c23ecf6211449c9bd7f4ac9229300ed43f666b2/projects/jsp-000636/PROVENANCE.md)
identifies our implementation and retains mathematical credit to He–Tang and
Erdős–Trotter. Direct-import inspection corroborates the stated dependency
boundary, but cannot by itself establish independent authorship.
[PR #677](https://github.com/TheJustinSunPrize/awards/pull/677) proposes a
stronger exact formula and predates our asymptotic supplement. We acknowledge
that work and request assessment of this separately implemented estimate proof;
no exact-formula, first-formalization or new-mathematics claim is made.

## JSP-000912

### Contribution and original statement

Our [standalone proof](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/bf99214b3104d89c628abb9c824a56d89a6bd6fe/projects/jsp-000912/FullProof.lean)
imports only Mathlib. Its explicit multiscale construction is connected to
`Nat.divisors n`, sorted in increasing order. `hAlpha` sums over the entire
list zipped with its tail; `sortedDivisors_neighbors` and
`sortedDivisors_zip_consecutive` connect those pairs to actual consecutive divisors.

The endpoint `jsp_000912_full` chooses a natural parameter with
`4 ≤ r*(α-1)` for every real `α > 1`, and supplies the positive witness
`candidate r M` at every cutoff `M`. The bound
`64*(16*r*(r+1)+2)^2` is independent of the cutoff.
Thus our formal contribution includes the explicit cofinal construction and
the full divisor-list argument, rather than only a finite-grid estimate.

### New evidence

We downloaded the six proof files at the recovered source commit
`9074d0cebd4e132a6c1fa71c0817693246935398` and the selected Lean 4.34 commit.
Applying the published
[LEAN4_34_PORT.patch](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/bf99214b3104d89c628abb9c824a56d89a6bd6fe/projects/jsp-000912/LEAN4_34_PORT.patch)
with zero fuzz **reconstructs all six selected files byte for byte**.
This includes the standalone file and five modular files; unchanged files are
also compared. The patch removes redundant trailing tactics, updates the
sorted-list API and simplifier arguments, and updates the environment header.
The mathematical definitions and theorem statements are preserved in this patch.

This is a reproducible connection between the preserved source and the current
verified implementation. It does not date the recovered source earlier than its
documented public history or apply old Lean 4.19 receipts to Lean 4.34.
The early PR revision is not evidence that the corrected complete proof was
already submitted then; the catalog was corrected at
[75faf61c9e78f62373287c0721916a2bd50556b4](https://github.com/ketianzhang1-lang/awards/commit/75faf61c9e78f62373287c0721916a2bd50556b4).

Michael D. Vose retains mathematical credit for the 1984 existence theorem.
A full formalization in `plby/lean-proofs` was already acknowledged in our
source header. We request credit for the documented implementation and
verification work, not first formalization.
See the [contribution statement](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/b4e47f3491c8278997b7998c535eee0eb7ccdc73/projects/jsp-000912/README.md#mathematical-source-and-requested-credit).

## JSP-000393

### Contribution and original statement

Our retained [integer-polynomial construction](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/17e406594d644b40c9a742e843cd6d89f319c872/JSP000393.lean)
proves the separated-exponent family counts `13^k` and `12^k` for every
natural `k`. The
[complete integration](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/17e406594d644b40c9a742e843cd6d89f319c872/JSP000393Complete.lean)
maps this family to rational coefficients while preserving support,
then proves `f(13^k) ≤ 12^k` for the actual attained minimum `Erdos485.f`.
Its `arbitrarily_large_small_ratio` theorem supplies, for **every** factor
`M` and cutoff `N`, an `n ≥ N` with `M*f(n) < n`.

The source-call chain is explicit:
`JSP000393.family_counts` → `rational_family_counts` →
`minimum_family_upper_bound` → `arbitrarily_large_small_ratio`.
The complete endpoint uses those conclusions alongside
`minimum_diverges := Erdos485.erdos_485`.
The divergence proof is imported, with its authorship retained.

### New evidence and verification repair

Our initial submission's
[SOURCE.json](https://github.com/ketianzhang1-lang/awards/blob/587d7724e74ac78235b9d9d63e4cbe5fc46ba20e/submissions/jsp-000393-kz-sparse-squares/SOURCE.json)
identifies `a337720331a34599114a9d4669d6518d5e608f6f` and the seed-file checksum.
That file is byte-identical at the original, selected and later verification commits.
The complete integration, `UPSTREAM.json` and dependency manifest are also
byte-identical between the selected proof and successful NaNoda verification
commit `0e86d155839b409faa075233a1b62e32f2b7b1e3`.
The public compare from the selected proof to the
[updated documentation](https://github.com/ketianzhang1-lang/jsp-000301-lean/compare/17e406594d644b40c9a742e843cd6d89f319c872...57bf1f4445d78e103f9424e420905fa56adbc469)
shows only workflow, verification-script, receipt, checksum and documentation
changes. The catalog should link those updated receipts while retaining the
selected proof commit.

For a bounded scope comparison, the later
[PR #921 source](https://github.com/Drag0ndddd1118/jsp-000393-formalization/blob/643f5a94e4264c7ab799877911c1de3e5d69bda4/JSP_000393.lean)
proves the concrete 13-term/12-term example in a list-polynomial model.
At that inspected commit, `Erdos1949AsymptoticSparsityStatement` is a
`def ... : Prop`, not a proof of that quantified statement.
Our all-`k` family, arbitrary-cutoff result and actual-minimum bridge are
therefore distinct contributions relative to that inspected file.
This observation neither judges a later revision nor establishes global priority.

Mathematical credit for the seed/amplification remains with Coppersmith–Davenport,
and for the general lower bound with Schinzel. The complete Schinzel formalization
comes from the pinned 22-module `plby/lean-proofs` closure, credited upstream
to Codex / GPT-5.6 Sol. Earlier full-result [registration #44](https://github.com/TheJustinSunPrize/awards/issues/44)
predates our integration. See the
[full provenance](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/17e406594d644b40c9a742e843cd6d89f319c872/PROVENANCE.md).

## JSP-000728

### Contribution and original statement

Our original [all-interval lower proof](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/22212651d30af02ad36f01a206984d31b0ec75c6/projects/jsp-000728/JSP000728.lean)
constructs odd-pair seeds, extends them to maximal sum-free sets, and injects
binary choices for every natural `N`, including zero.
The [bridge module](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/22212651d30af02ad36f01a206984d31b0ec75c6/projects/jsp-000728/JSP000728Bridge.lean)
proves predicate equivalence and equality of actual families/counts, and embeds
the upper-half powerset to obtain `F(N) ≥ 2^ceil(N/2)`.

The [complete module](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/22212651d30af02ad36f01a206984d31b0ec75c6/projects/jsp-000728/JSP000728Complete.lean)
combines the imported exponential upper bound with that benchmark to prove
`M(N)/F(N) → 0` and fixed exponential separation from `F(N)`.
Its final conjunction includes our `cameron_erdos_lower_bound` directly;
`upstream_count_lower_bound` also transports that theorem to the imported count.

### New evidence and division of credit

The original lower proof at `91fdee92a0e9122b9e41cfd3b24d0ab70a64b3c0`,
the file preserved in the
[initial catalog-submission history](https://github.com/ketianzhang1-lang/awards/blob/fa77d5ecf712a1e0fadfdd642eeaf50ac1162968/docs/submissions/jsp-000728-kz/JSP000728.lean),
and the selected complete-project version are **byte-identical**.
The supplementary verifier also checks the relevant source-call markers.

This gives a concrete retained implementation plus explicit count-model
integration. The maximal-count lower bound is a component of the combined
endpoint; the relative upper-bound argument relies on the imported upper proof
and our upper-half benchmark, not on that maximal-count lower bound.
Our original partial submission is not represented as an earlier complete solution.

The 43-module upper proof is reused with full attribution from `plby/lean-proofs`
at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
Cameron–Erdős retain credit for the classical lower construction, Łuczak–Schoen
for the original exponential separation, and Balogh–Liu–Sharifzadeh–Treglown for
later sharper results. The later sharp exponent 1/4 and residue-class constants
are not part of this submission. See
[PROVENANCE.md](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/22212651d30af02ad36f01a206984d31b0ec75c6/projects/jsp-000728/PROVENANCE.md)
for the prior upstream result and retained licenses.

## Verification records and limits

The following existing public workflows were queried successfully on 2026-09-19.
All four returned `success` at the listed commits. This source audit does not
claim to have freshly run Lean or NaNoda.

| Problem | Public workflow | Verified commit |
| --- | --- | --- |
| 636 | [35296708689](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35296708689) | `5c23ecf6211449c9bd7f4ac9229300ed43f666b2` |
| 912 | [35265836287](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35265836287) | `bf99214b3104d89c628abb9c824a56d89a6bd6fe` |
| 393 | [35302255801](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35302255801) | `0e86d155839b409faa075233a1b62e32f2b7b1e3` |
| 728 | [35300095687](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35300095687) | `22212651d30af02ad36f01a206984d31b0ec75c6` |

[sources.json](sources.json) records immutable URLs, byte counts, SHA-256 and
Git blob hashes for 44 inspected source snapshots.
Run [verify_source_bindings.py](verify_source_bindings.py) beside it:

```bash
python3 verify_source_bindings.py
```

Python 3, GNU patch and network access are required. It verifies the source
bindings and the comparisons described above; source-call markers are a
supplement to source inspection, not semantic proof checking.
All these comparisons passed during preparation. Complete Lean reproduction
commands and dependency pins remain in each proof project's linked README.

The review request is to assess each complete submission and the named
contributor's identified additional implementation/integration work, with
prior work credited. Repository ownership, matching bytes, an earlier partial
PR, and successful automated checks do not establish authorship, worldwide
priority, maintainer approval or award entitlement. Eligibility and payment
decisions remain with the organizers.

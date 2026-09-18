# Priority evidence supplement: JSP-000391 and JSP-000438

Prepared on 2026-09-18 for the existing Lean-formalization applications by `ketianzhang1-lang`, with disclosed OpenAI ChatGPT/Codex assistance. This note supplements [claim #1352](https://github.com/TheJustinSunPrize/awards/issues/1352) / [PR #293](https://github.com/TheJustinSunPrize/awards/pull/293) and [claim #1410](https://github.com/TheJustinSunPrize/awards/issues/1410) / [PR #408](https://github.com/TheJustinSunPrize/awards/pull/408). It creates no separate award claim.

## Findings and requested review

The historical PR revisions contain the complete arbitrary-base digit construction (391) and the all-order tree Ramsey upper bound (438). Their core Lean files have exactly the same Git blob identifiers as both the early successful CI source and the selected proof versions. This gives a reproducible content link across the three versions; it does not assign a first-publication time to them.

For 391, a later contributor's fixed-version provenance notice additionally identifies these exact earlier proof files as inspected prior work. For 438, the contribution is an integration of a credited, existing Erdős–Sós proof into the complete tree Ramsey result; ownership of that dependency is not claimed.

Please assess the relative priority and attributable contribution to each complete formalization, resolve the pending catalog updates and account-to-contributor verification, and apply the organizers' award rules. No global first-publication finding, independent human certification, exclusive entitlement, or award approval is asserted by this note.

## JSP-000391: complete arbitrary-base construction

### Scope and version identity

The [historical main theorem file](https://github.com/TheJustinSunPrize/awards/blob/8d5b80f51a4df0b010fe7e6a079dcc5cdfab0b00/docs/submissions/jsp-000391-kz/JSP000391Main.lean) contains `stoll_general_base` for every integer radix `g ≥ 2`, positive real `w`, and admissible shift. It includes recurrence-to-digit identities, digit bounds, normalized-prefix reconstruction, and the explicit admissible-shift corollary `jsp000391`. Mathematical credit remains with Thomas Stoll and the prior literature.

| Version | Commit and source directory |
| --- | --- |
| Early successful CI source | [`56f083c6183e93eeffc334e04e39a26548bfae96`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/56f083c6183e93eeffc334e04e39a26548bfae96/projects/jsp-000391) |
| Historical PR source bundle | [`8d5b80f51a4df0b010fe7e6a079dcc5cdfab0b00`](https://github.com/TheJustinSunPrize/awards/tree/8d5b80f51a4df0b010fe7e6a079dcc5cdfab0b00/docs/submissions/jsp-000391-kz) |
| Selected proof version in the application | [`14e5155e68554de4e053e4aacd77095a93e96dd4`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/14e5155e68554de4e053e4aacd77095a93e96dd4/projects/jsp-000391) |

The following six files have identical blob IDs in all three versions:

| File | Shared Git blob SHA |
| --- | --- |
| `JSP000391.lean` | `f28358fd14b979241183793faf6f019711499cfd` |
| `JSP000391Main.lean` | `f14b3bc007ca72454e9835053c8c9e057702fa56` |
| `Audit.lean` | `e6649cd56499a91f708243df8adb041ad6399cf5` |
| `lean-toolchain` | `12359f928f18e4a89ebd1444a0310b025931b17d` |
| `lakefile.lean` | `6e9f101c121fb7ed5c387ff33d35e6c89bc10a34` |
| `lake-manifest.json` | `5e8019ae3c4ab1fc28cd3e7d429a8b896a2ab306` |

Documentation and packaging are not asserted to be identical. The content comparison is not a new proof rebuild.

### Execution and submission records (UTC)

| Record | Timestamp | Meaning |
| --- | --- | --- |
| [CI run 35157931469](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35157931469) started | 2026-09-16 22:29:30 | GitHub run timestamp, exact head SHA listed above |
| [Verification job 105001695072](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35157931469/job/105001695072) completed successfully | 2026-09-16 22:33:05 | Build, kernel replay, eight-target axiom audit, NaNoda verification, and archive steps report success |
| Historical PR bundle commit | 2026-09-16 22:37:34 | Git committer timestamp, not a server publication timestamp |
| PR #293 created | 2026-09-16 22:43:45 | GitHub PR record creation |
| [Later PR #1163](https://github.com/TheJustinSunPrize/awards/pull/1163) created | 2026-09-18 10:42:34 | GitHub PR record creation |

The current PR history records a later [catalog-reference conversion](https://github.com/TheJustinSunPrize/awards/commit/23afb522b6881a6d46e297c91a787720762bbabd). Historical source-bundle files remain accessible at their commit. These are PR-history revisions, not evidence that the organizer merged or accepted the proof.

### Third-party acknowledgement and earlier scope

[PengSafari's NOTICE at commit `8beb80b`](https://github.com/PengSafari/jsp-000391-lean/blob/8beb80bbe38682395de5afb7b33e7fa05ad72637/NOTICE.md) identifies PR #293 and `JSP000391.lean` / `JSP000391Main.lean` at `14e5155e68554de4e053e4aacd77095a93e96dd4` as earlier work read during problem selection. It describes subsequent implementation in that contributor's own modules and does not claim first-formalization priority. This is evidence of acknowledged relative provenance with respect to that submission, not a waiver of another contributor's rights or a determination of global priority.

The [earlier plby Erdős 482 formalization](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos482.lean) supplies the binary case. The relevant scope difference here is the complete arbitrary-base construction. The original claim already discloses that earlier work.

## JSP-000438: complete all-order tree Ramsey bound

### Scope, reuse, and version identity

The [historical main file](https://github.com/TheJustinSunPrize/awards/blob/167ed0362b8041f5b3b52fde8bcac8be6a1755bf/docs/submissions/jsp-000438-kz/JSP000438.lean) already proves `Erdos547.erdos_547` for every `n ≥ 2`: each `n`-vertex tree has diagonal graph Ramsey number at most `2n − 2`. It also contains the asymmetric `m+n−2` bound. The proof invokes the existing `Erdos548.tree_free_edge_bound`, rather than assuming it as a new axiom.

| Version | Commit and source directory |
| --- | --- |
| Early successful CI source | [`11a32e130fa669a4f23f0bbe7a320fd9675dbb7c`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/11a32e130fa669a4f23f0bbe7a320fd9675dbb7c/projects/jsp-000438) |
| Historical PR source bundle | [`167ed0362b8041f5b3b52fde8bcac8be6a1755bf`](https://github.com/TheJustinSunPrize/awards/tree/167ed0362b8041f5b3b52fde8bcac8be6a1755bf/docs/submissions/jsp-000438-kz) |
| Selected proof version in the application | [`5f94d026ec88696bb5047506c433ad401e5f02ef`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/5f94d026ec88696bb5047506c433ad401e5f02ef/projects/jsp-000438) |

The three core modules and the following two configuration files have identical blob IDs in all three versions:

| File | Shared Git blob SHA |
| --- | --- |
| `JSP000438.lean` | `7cdd90a6b8f933404d95933301a96fc459d5d3e6` |
| `RamseyDefinitions.lean` | `bd6657a10724e35e27c72aecf85678e5079ad1e6` |
| `Upstream548.lean` | `2688ec02d4f8bfd1e0fe0d7f1c46f4e58a5ac314` |
| `lean-toolchain` | `12359f928f18e4a89ebd1444a0310b025931b17d` |
| `lake-manifest.json` | `28cf830485a5111d8ea1695808c44c605b08e546` |

The later selected package also contains star sharpness and other audit/build additions. `Audit.lean` and `lakefile.lean` changed; the whole package is not byte-identical. This early evidence applies to the all-order upper bound. The finite-color and star supplements have their own later PR commits ([finite-color](https://github.com/TheJustinSunPrize/awards/commit/6fd24e484966821113a2ad7c3c7cabaf63bb8ab4), [star sharpness](https://github.com/TheJustinSunPrize/awards/commit/30be5646a4dffff8b40227d65da5ef0f6afc01f5)) and are not backdated to the original upper-bound CI run.

### Execution and submission records (UTC)

| Record | Timestamp | Meaning |
| --- | --- | --- |
| [CI run 35175029806](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35175029806) started | 2026-09-17 02:35:56 | GitHub run timestamp, exact head SHA listed above |
| [Verification job 105054732657](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35175029806/job/105054732657) completed successfully | 2026-09-17 02:38:50 | Build, replay, five axiom audits, negative control, NaNoda verification, and archive steps report success |
| Historical PR bundle commit | 2026-09-17 02:49:13 | Git committer timestamp, not a server publication timestamp |
| PR #408 created | 2026-09-17 02:51:34 | GitHub PR record creation |

The current PR history records a later [catalog-only conversion](https://github.com/TheJustinSunPrize/awards/commit/496f3bab5f4025a1475e19b85495d34f9866ea60). The source comparison above links the historical bundle to the selected proof; it does not depend on the current editable PR description having existed at opening.

### Attributable contribution

The [previous plby Erdős 547 treatment](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos547.lean) supplies a conditional reduction and the sufficiently-large case. The disclosed contribution here is the complete all-order Ramsey integration, statement alignment, compatibility port, and subsequent supplements.

The Erdős–Sós dependency comes from [tadamcz/erdos548 at `82ffb75`](https://github.com/tadamcz/erdos548/blob/82ffb751f3d37768927df9239ed08439bbe0dd09/Erdos548/Resolutions/Erdos548_192usd_21h.lean). The [NOTICE](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5f94d026ec88696bb5047506c433ad401e5f02ef/projects/jsp-000438/NOTICE) and [port record](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5f94d026ec88696bb5047506c433ad401e5f02ef/projects/jsp-000438/UPSTREAM_PORT.md) preserve the upstream credits, including Tom Adamczewski / Epoch AI, Thomas F. Bloom, FrontierMath and GPT-6 Astra (OpenAI), and the Formal Conjectures attribution. No mathematical-discovery or upstream-proof authorship is claimed here.

## Artifact receipts and reproducibility

The [machine-readable evidence](evidence.json) records the GitHub query URLs, observation times where recorded, commit IDs, comparison hashes, CI status/step summaries, and service-reported artifact digests. The early run artifacts currently report:

| Problem | Artifact ID | Size | GitHub-reported SHA-256 |
| --- | --- | --- | --- |
| 391 | 10471333076 | 12,170,425 bytes | `ed182bb56a1e1f3986c65593f428afd9df1bcd71a3005895a74a1fd2fb1912ca` |
| 438 | 10478133208 | 8,112,880 bytes | `fb1405c9051fba1bfb217242478d0c96e79ba155ea9b98a804533929263f17df` |

These digest values are API metadata, not newly computed hashes of downloaded ZIP files. No artifact ZIP was downloaded in preparing this supplement. In particular, the [historical 438 receipt](https://github.com/TheJustinSunPrize/awards/blob/167ed0362b8041f5b3b52fde8bcac8be6a1755bf/docs/submissions/jsp-000438-kz/VERIFICATION.md) reports that its archive transfer was unavailable; this note does not upgrade that to a locally verified archive. The source and compact verification receipts remain accessible as Git files.

To reproduce the content comparison, query the early and selected commit directories through GitHub's Contents API and the historical PR commit through its Commit API. Match the file names and blob IDs listed above. Raw contents can also be checked with `git hash-object`. For a new formal verification, use the corresponding commit's pinned toolchain, locked dependencies and verification scripts; this note reports historical execution rather than a fresh run.

## Limits of the chronology

Git author/committer dates are user-controlled. GitHub CI timestamps establish execution timing, not repository visibility at that instant. PR creation times establish the PR record; current commit membership, editable PR descriptions, and Git dates alone do not prove the exact source publicly visible when a PR opened. This review did not obtain a complete archive of visibility changes, description edits or force pushes.

The conclusions are therefore limited to reproducible proof-content continuity, historical successful execution, the recorded PR chronology, and the explicit third-party acknowledgement for 391. The exact first-publication date, complete cross-platform priority, award eligibility, identity verification, attribution allocation and payment remain for organizer review. Both applications and catalog PRs were open and unmerged at the inspected snapshot; this supplement is not organizer endorsement.

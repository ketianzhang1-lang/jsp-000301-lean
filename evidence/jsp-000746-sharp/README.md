# JSP-000746 / Erdos 895: verified sharpness supplement

## Precisely what this adds

Let P(n) mean that every triangle-free simple graph on the labeled vertices {1,...,n} contains three distinct pairwise nonadjacent vertices a,b,a+b, with a<b. The new Lean theorem proves **P(n) if and only if n >= 18**, for every natural n, including zero.

The new contribution is an explicit 43-edge counterexample on 17 vertices, its formal restriction to every n<=17, and the exact-threshold equivalence obtained by combining this with the **unchanged, previously published** upper-bound proof.

This is a formalization supplement, **not a new mathematical solution or a first formalization of the original problem**. No exclusive priority, prize allocation, or payment is asserted. The stronger Hindman-set question is not claimed. The finite theorem implies the original existence assertion on the integers by restriction to positive labels 1,...,18; this file does not add a separately named integer-graph corollary.

## Attribution and existing evidence

- Mathematical upper-bound result: Ben Barber, as credited in the original source and official catalog.
- Reused formal upper-bound source: plby/lean-proofs, crediting Codex and GPT-5.6 Sol.
- New witness/formal restriction/threshold code and Python checkers: prepared with OpenAI ChatGPT assistance for the submitting account. Public recipient confirmation is pending; no unconfirmed legal identity is asserted.
- [Existing official evidence issue #19](https://github.com/TheJustinSunPrize/awards/issues/19) already covers the sufficiency of 18 and explicitly excludes a sharpness claim. This supplement does not replace that contribution or reassign its credit.

The existing source describes the threshold as sharp in prose but its Lean declarations prove only the sufficient upper bound. This supplement supplies the missing formal lower-bound direction. A wider priority and significance review remains for maintainers.

## Successful Lean verification

[Successful workflow run #4](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35172135809), completed September 17, 2026 UTC (September 16 in America/New_York):

- Proof commit: `b62eb3c313e08907fc76fe927cf28545a38178e0`.
- [Pinned new source](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/b62eb3c313e08907fc76fe927cf28545a38178e0/projects/jsp-000746-sharp/JSP000746Sharp.lean).
- New source SHA-256: `8f3ffdbdc222b94abe89e74413833f011880651136767e8b8cc3fe90190803b2`.
- Lean: `4.33.0`; Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Upstream source and certificate commit: `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` in plby/lean-proofs.
- [Evidence artifact](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35172135809/artifacts/10476738843), ID `10476738843`.
- Artifact ZIP SHA-256: `e8931676c8664efe515edab27190b5f92f706af6bbafa1b9116650914194099f`.

Both the unchanged upstream module and the new module compiled with `-DwarningAsError=true`. All seven audited new declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; none depends on `sorryAx` or `Lean.ofReduceBool`. Finite checks use `decide`, not `native_decide`.

The seven audited declarations in namespace `JSP000746Sharp` are:

```
no_triangles
schur_coverage
witness_triangle_free
witness_no_independent_schur_triple
counterexamples_below_eighteen
exact_threshold
least_threshold
```

`leanchecker --verbose Erdos895` and `leanchecker --verbose JSP000746Sharp` both completed successfully. A negative-control module importing the result and attempting `example : (2 : Nat) + 2 = 5 := by decide` was rejected with the diagnostic that this proposition is false.

The artifact was downloaded and every file hash in its manifest checked. Its Lean source matches the published proof source byte for byte. Earlier runs are failures and are not offered as successful evidence: run 1 used an unsupported CLI option; run 2 exceeded its memory cap; run 3 exposed two structure-interface errors that were repaired before this successful run. No mathematical assumption was added by those repairs.

## Independent finite cross-checks

The standard-library Python witness checker compares the one-based edge list with the exact Lean edge list, checks all 680 unordered triples and all 64 distinct-summand Schur triples on 17 vertices, and tests each initial interval n=0,...,17. All checks pass. It detects both a deliberately introduced triangle and deletion of an essential covering edge.

The independent RUP checker reconstructs the 18-vertex graph encoding clause by clause: 153 edge variables, 816 triangle clauses, and 72 Schur-coverage clauses. It verifies all 2,076 RUP clause additions, 747 deletions, and 33,999 unit/conflict hint steps, deriving the empty clause. Removing final proof hints or corrupting the graph encoding is rejected. Unsupported RAT hints are rejected rather than trusted.

The logical argument is complete at finite level: the 17-vertex witness restricts to every smaller initial interval; unsatisfiability proves the forcing property on 18 labels; restriction to the first 18 labels handles every larger n.

These Python checks were executed separately from the Lean CI. They are an independent finite verification implementation, **not an independently implemented Lean kernel**. `leanchecker` is a replay with Lean's kernel, not a second kernel implementation. Human statement, attribution, and award review remain necessary.

## Reproduction

From a checkout containing this directory, with Python 3.10 or later:

```sh
python3 evidence/jsp-000746-sharp/fetch_inputs.py
python3 evidence/jsp-000746-sharp/verify_witness.py
python3 evidence/jsp-000746-sharp/check_lrat.py
```

The fetcher downloads only immutable public upstream files and refuses a SHA-256 mismatch. The checkers produce `witness-report.json` (including all 64 coverage rows) and `lrat-report.json`. Original upstream attribution remains in its source; no authorship or license transfer is asserted.

For the exact Lean build environment and commands, use the [pinned successful workflow](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/b62eb3c313e08907fc76fe927cf28545a38178e0/.github/workflows/jsp-000746-sharp.yml). On the successful Linux runner, certificate reconstruction required more than the earlier 6 GiB cap; the successful workflow provides swap headroom and a 12 GiB Lean cap. It preserves source, certificates, version, dependency manifest, build logs, axiom reports, replay logs, and negative-control output in the artifact.

## Award boundary

This is evidence for review of the **incremental formalization contribution only**. It is not a completed official verification record, a confirmation of recipient identity, an announcement of an award, or a request to reassign the already existing upper-bound contribution. See the official [contribution guide](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md) and [verification guide](https://github.com/TheJustinSunPrize/awards/blob/main/docs/verification.md).

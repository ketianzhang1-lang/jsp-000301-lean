# JSP-000254 submission receipt

Proof source: [54a0d8edb05945100ff151f70e8dc28870a45962](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/54a0d8edb05945100ff151f70e8dc28870a45962/projects/jsp-000254).

Verification: [successful run 35173758386](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35173758386). All 12 target axiom audits passed; NaNoda checked 12,948 declarations with no errors. Artifact ID 10477866850; GitHub-reported SHA-256: `043167e9e4f3f4dc9936a1794e1013f0d20a10b95c8a2601340aa7914cd47c07`. The ZIP was not independently downloaded and rehashed here.

Submission package: [c938be0bdb95ac460eba311cb8cc8abbd6f123bd](https://github.com/ketianzhang1-lang/awards/tree/c938be0bdb95ac460eba311cb8cc8abbd6f123bd/docs/submissions/jsp-000254-kz).

Status on 2026-09-17: proof and package published; the automatic upstream PR creation was rejected with GitHub API 403. No upstream PR was created by that attempt. Manual creation remains necessary. No award or payment is claimed.

## Prepared PR title

Submit JSP-000254 Cambie lower bound and half-density disproof (partial scope)

## Prepared PR body

This adds a formalization evidence package for the known Cambie lower bound in JSP-000254 / Erdős 302.

The proof constructs an admissible subset of {1,...,N} of exactly 5 floor(N/8) elements for every N, proves the asymptotic 5/8 lower bound, and completely refutes the separate conjecture that f(N)/N tends to 1/2. The maximum-cardinality function is explicitly defined and proved to exist.

**Scope:** this does not determine the optimal density, establish existence of its limit, or settle the full catalog problem. The mathematics is Stijn Cambie's known construction; the contribution submitted for review is the new Lean proof scripts and verification package, prepared with OpenAI Codex assistance. No original mathematical discovery or globally first formalization claim is made.

Fixed source: [54a0d8edb05945100ff151f70e8dc28870a45962](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/54a0d8edb05945100ff151f70e8dc28870a45962/projects/jsp-000254).
Proof CI: [run 35173758386](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35173758386).

The package maps the proved statements to `Erdos302.erdos_302.variants.lower_five_eighths` and `Erdos302.erdos_302.parts.ii` in the fixed formal-conjectures snapshot. Both upstream theorem bodies are admitted there. Their definitions and statement types are preserved, and no admitted upstream module is imported.

Verification: Lean 4.34.0 / pinned Mathlib, warnings-as-errors compilation, leanchecker, all 12 target axiom audits, dependency revision checks, false-arithmetic negative control, and independent NaNoda replay. Exact execution and artifact metadata are recorded in `evidence.json`.

Repository validation: validate, links, build, check, history, and all 22 tests passed. The PR adds three documentation/evidence files only. It does not modify catalog statuses, claim eligibility, live candidate/award records, or payment records.

Formalization attribution uses `RECIPIENT-JSP-000254-KZ-A` (submitting account `ketianzhang1-lang`). No recipient identity confirmation or independent human review is asserted. The submitter has an interest in assessment of this contribution. Please review the mathematical scope and formalization evidence through the normal process.

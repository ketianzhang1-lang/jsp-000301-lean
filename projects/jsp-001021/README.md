# JSP-001021: complete tournament disproof with order transport and checked local certificates

We provide a complete Lean disproof of the proposed universal tournament formula, together with a fifteen-vertex endpoint and kernel-checked local certificates from our mathematical reproduction. For every tournament on n >= 14 vertices, the integrated development supplies an injectively ordered transitive five-vertex subtournament. In particular, the guaranteed size at n=15 is at least five, whereas the proposed formula gives four.

## Our formalization contribution

Our contribution, recorded under GitHub account `ketianzhang1-lang` and developed with OpenAI ChatGPT assistance, comprises:

1. An explicit fourteen-vertex restriction encoding and a proof that it preserves every edge orientation.
2. Transport of the attributed fourteen-vertex result to every order n >= 14, including a dedicated fifteen-vertex theorem.
3. A lower bound for the exact extremal function at fifteen and a direct negation of the proposed universal equality at that order.
4. Kernel-checked local exclusion certificates covering all 196 ordered pairs of cyclic triples, the count of 42 retained patterns and the final ordered transitive five-set in our reproduction.
5. A pinned Lean 4.34 project with exact-type checks, dependency and axiom audits, complete module replay and a negative control.

The complete main proof uses the credited Reid–Parker fourteen-vertex formalization. Our earlier independent mathematical reconstruction remains in [reproduction/PROOF.md](reproduction/PROOF.md); its local finite checks are now formalized, but we do not claim that every step of that separate reconstruction has been ported to Lean. [PROVENANCE.md](PROVENANCE.md) distinguishes these contributions.

## Complete theorem and scope

In [JSP001021.lean](JSP001021.lean):

- `JSP001021.restrict14_arc` proves that the restriction preserves orientation.
- `JSP001021.all_orders` proves the transitive-five conclusion at every n >= 14.
- `JSP001021.fifteen_vertices` states the result for every fifteen-vertex tournament.
- `JSP001021.five_le_f_fifteen` proves `5 <= Erdos1216.f 15`.
- `JSP001021.jsp_001021` negates `∀ n >= 1, f(n) = Nat.log2 n + 1`.

The imported `Erdos1216.f` is the greatest size guaranteed in every tournament of the given order. A transitive subtournament is an injective ordered vertex map whose every forward edge has the required orientation. All tournaments of each stated order are quantified over; no sample of tournaments or extra unproved combinatorial hypothesis is used. One counterexample order completely refutes the proposed universal formula; determining the exact function at every order is a different problem.

In [FiniteChecks.lean](FiniteChecks.lean), `local_exclusions` checks 196 pairs: 70 fail the required intersection condition, 84 have an explicit transitive-five witness, and 42 fall into the retained pattern families. `retained_count` and `final_transitive_five` check the count and final ten forward edges. These local checks use ordinary `decide` with kernel verification.

## Reproduce

- Repository: https://github.com/ketianzhang1-lang/jsp-000301-lean
- Branch: `jsp-001021-tournament-verification`
- Project: `projects/jsp-001021`
- Lean 4.34.0; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
- Transitive dependency revisions: `lake-manifest.json`.

Check out the exact full commit selected in [PR #699](https://github.com/TheJustinSunPrize/awards/pull/699), enter the project directory, and run:

```bash
python3 scripts/bootstrap.py
lake exe cache get Mathlib.Tactic Mathlib.Data.Finset.Sort Mathlib.Tactic.IntervalCases Mathlib.LinearAlgebra.Matrix.Notation
bash scripts/verify.sh
```

Bootstrap verifies the two immutable upstream file hashes. The script compiles all four proof modules with warnings treated as errors, replays each module, audits eleven theorem closures, checks the exact public statements and actual dependency revisions, and rejects false arithmetic. Keep the committed dependency manifest. The upstream finite certificates are substantial and require memory headroom; the workflow supplies swap.

The separate Python reproduction remains available as `python3 reproduction/verify.py`. Its output is supplementary evidence; the Lean proof has its own complete dependency chain and kernel checks. See [VERIFICATION.md](VERIFICATION.md).

## Attribution and requested review

We request credit for our restriction and transport implementation, fifteen-vertex disproof integration, local finite certificates and reproduction package. Mathematical credit remains with K. B. Reid and E. T. Parker. The substantive fourteen-vertex Lean proof and its branching certificates retain their upstream Codex / GPT-5.6 Sol attribution. We make no mathematical-discovery or first-formalization claim. Acceptance and contribution eligibility remain subject to organizer review.


## Independent NaNoda verification — 2026-09-18

We independently checked all 11 audited target dependency closures with NaNoda in [run 35302257717](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35302257717), at commit `3ebcc72d98b50f59ff456feb5963f85815b2d09c`. The checker reported **6,715 declarations with no errors**, and statement printing also succeeded. The same run passed source compilation, four Lean kernel replays, the original eleven axiom audits, exact-statement checks, dependency revision checks and the false-arithmetic negative control.

The export includes the complete universal negation `JSP001021.jsp_001021`, our fifteen-vertex result, the upstream fourteen-vertex theorems and all other targets in `Audit.lean`. Every target is exported with its full dependency closure. Only `propext`, `Classical.choice` and `Quot.sound` are permitted, with `unpermitted_axiom_hard_error: true`; no `sorryAx`, compiler-trust axiom or custom unproved axiom is allowed.

[The source comparison](https://github.com/ketianzhang1-lang/jsp-000301-lean/compare/7642a7f5eb190da6319b6ae7f11c829d7737e2dd...3ebcc72d98b50f59ff456feb5963f85815b2d09c) confirms that the Lean proof files, upstream source pins and dependency manifest are unchanged from the selected proof commit `7642a7f5eb190da6319b6ae7f11c829d7737e2dd`. We added checker integration and evidence collection; no mathematical proof repair was needed.

To reproduce this additional check, check out `3ebcc72d98b50f59ff456feb5963f85815b2d09c`, enter `projects/jsp-001021`, run the documented bootstrap, dependency-cache setup and full `bash scripts/verify.sh` sequence, then run:

```bash
bash scripts/verify_nanoda.sh
```

The checker script pins lean4export to `6cea97789dc088ea47fcea15692db85685aedac5` and NaNoda to `4c544ed4099c8227f07d5de77ad1e69fb0740a27`, builds them from source and requires error-free checking and nonempty statement output. Git, Python 3, Lean/Lake and Rust/Cargo with network access are required. The public CI performs the whole sequence. The finite certificates require substantial computation and memory, so the workflow provides swap space.

[The machine-readable CI receipt](verification/nanoda-ci.json) records the exact run, source comparison, checked targets and artifact digest. The workflow artifact includes the compressed exported proof, checker configuration, printed statements and logs under `nanoda/` and is retained for 90 days. NaNoda is a separately implemented checker; this contributor-run verification is not independent human review or organizer approval.

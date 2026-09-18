# JSP-000554: complete prime-gap density and our exact residue classification

We extend our exact finite residue formalization with a bridge to the existing
complete density-one proof of Gafni--Tao's result. The proposed complete endpoint
is `JSP000554.jsp_000554` in `JSP000554Complete.lean`.

**Verification of this integration is in progress. This revision does not yet
claim a successful complete build or NaNoda run.** The earlier partial proof and
its successful checks remain in Git history and `INITIAL_PARTIAL_README.md`.

Our original 23 theorems remain unchanged. We add 12 public integration theorems
and a pinned verification package. The complete analytic proof is an attributed
dependency from plby/lean-proofs, not our original proof. See `PROVENANCE.md`
and `STATEMENT_FIDELITY.md` for the exact contribution and quantifiers.

With Lean 4.34.0 and the committed dependency manifest, run:

```bash
python3 scripts/bootstrap.py
lake exe cache get Mathlib
lake build Mathlib
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

Git, Python 3, Lean/Lake, Rust/Cargo and network access are required. The pinned
51-module upstream closure is fetched and hash-verified before compilation.
The full verification checks 54 modules and 37 selected theorem dependency
closures, with only `propext`, `Classical.choice` and `Quot.sound` permitted.
Actual execution results will be recorded after these commands pass.

We request review of our formalization and integration contribution. No award
eligibility, first-formalization priority or organizer approval is implied.

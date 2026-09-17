# Verification receipt — JSP-000636 pair-label supplement

## Scope and baseline

This extends proof commit `3e3bb53650eda1f183b5af89ea3f6747349c06a4`.
The inherited `JSP000636.lean`, `Lower.lean`, and dependency manifest are
byte-identical to that commit. New mathematical code is in `Upper.lean`,
`Construction.lean`, `Threshold.lean`, and `Thinning.lean`.

## Checks actually completed locally

- Lean 4.34.0 compiled all six modules with `warningAsError=true`.
- All 61 theorem dependency audits allow only `propext`, `Classical.choice`,
  and `Quot.sound`; no `sorryAx` or custom axiom appears.
- Lean's bundled `leanchecker` replayed all four new modules successfully.
- The pinned dependency manifest matches the verified baseline. Local cache
  Git revisions could not all be checked because its Mathlib checkout lacks HEAD;
  fresh CI must verify dependency revisions before a reproducibility claim.
- The false arithmetic negative control `1 = 0` was rejected.
- Both reproduction shell scripts passed syntax checking.

Local execution used a compiler path compatibility shim and an existing
pinned Mathlib cache. Lean's bundled checker is a replay with the same
kernel implementation, not an independent implementation. The CI workflow
uses a fresh Ubuntu runner and additionally requests the separately
implemented NaNoda checker with the same strict three-axiom allowlist.

At creation of this receipt, fresh CI/NaNoda results for the supplement
were pending. Do not treat configuration of a check as a successful run.

These checks validate the formal statements. They do not establish full
resolution of JSP-000636, global priority, human mathematical review,
organizer acceptance, eligibility or payment.

# Verification of the complete JSP-000140 package

The scripts in this revision are being executed against 24 source modules
and 46 selected theorem dependency closures. The complete hosted result will
be recorded after the run finishes. A workflow definition is not a pass.

The selected roots include all 44 public lemmas/theorems in our three modules
and both complete imported asymptotic endpoints. Only propext, Classical.choice
and Quot.sound are permitted. Existing files under evidence relate to the
previous lower-bound-only proof and do not certify the completed package.

README.md gives pinned fresh-checkout commands. The bootstrap verifies both
original and compatibility-port source hashes. The checker scripts compile
with warnings treated as errors, replay proof modules, audit dependencies and
axioms, reject the false arithmetic statement 1 = 0, and run pinned NaNoda.

# Verification of the complete JSP-000585 package

This revision provides reproducible Lean and independent NaNoda scripts for all
66 source modules and 61 theorem-closure targets. The source includes the 56 pinned
upstream modules, seven unchanged original modules, two new modules and the audit.
Only propext, Classical.choice and Quot.sound are permitted axioms. Any other
axiom, including sorryAx or a compiler-trust axiom, is a verification failure.

The current complete checks and their executed receipts will be recorded after
the hosted run finishes. Older files under evidence/local-build.log and
evidence/local-axioms.log relate only to the earlier finite proof and do not
establish a pass for this complete package. README.md gives fresh-checkout commands.

# Verification status

The complete 38-module upstream dependency closure and all four new local
proof modules have compiled locally with Lean 4.34.0 and warnings treated
as errors. The standardized 43-module build, 35 theorem-closure audits,
full kernel replay and independent NaNoda check are being executed.

This pre-verification record does not claim that the independent check has
passed. A later documentation receipt will identify the selected exact
proof commit, public CI run, checker output and actual declaration count.

Reproduction commands are in README.md. AUDIT_TARGETS.json lists all 35
targets. Only propext, Classical.choice and Quot.sound are permitted. The
negative control attempts the false statement `(1 : Nat) = 0` after loading
the complete proof.

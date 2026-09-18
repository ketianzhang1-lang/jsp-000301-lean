# Verification of the integrated JSP-000506 development

Full verification is in progress. Do not treat preparation/cache workflow
success as a successful complete proof check. The preceding finite theorem's
receipt is preserved in `INITIAL_PARTIAL_VERIFICATION.md`.

The integrated checks are reproducible with `scripts/verify.sh` followed by
`scripts/verify_nanoda.sh`. They cover strict compilation of the unchanged
480-module upstream closure, the original finite proof and two new bridge
modules; 49 axiom audits; four Lean kernel replay prefixes; a false-arithmetic
negative control; and independent NaNoda checking of the audited closures.
A final receipt will identify the actual tested source commit and run.

# JSP-000250 verification

Status: local compilation of all 78 modules and all 21 axiom-closure audits
have passed for the complete integrated proof. The published source also adds
explicit modification notices to compatibility-ported source files.

A clean hosted run must verify this published revision through compilation,
kernel replay, the negative control and independent strict-allowlist NaNoda
checking. Those hosted results are pending; the earlier upper-only receipt
does not validate the complete endpoint.

Reproduction is implemented in `scripts/verify.sh` and
`scripts/verify_nanoda.sh`. Completed results and immutable proof identification
will be recorded after the hosted checks finish.

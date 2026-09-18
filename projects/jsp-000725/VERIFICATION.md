# Executed verification of JSP-000725

The complete proof at commit **`d0d37952bba030d7c8a68f000094e0d601d9fed7`** passed the
[public workflow run 35308272360](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35308272360). The run's `head_sha`
matches this exact proof commit on branch `jsp-000725-interval`.

## Checks actually passed

- **46 source modules** compiled with warnings treated as errors: 42 pinned
  upstream modules, our three proof modules, and the audit module.
- **28 theorem-closure axiom audits** passed. The audited set includes every
  public theorem in our modules and the two complete imported endpoints.
- Only `propext`, `Classical.choice`, and `Quot.sound` occur. No `sorryAx`,
  compiler-trust axiom, or added custom axiom occurs in these theorem closures.
- Lean kernel replay passed for every one of the 42 upstream modules and for
  our original construction, statement bridge and complete endpoint.
- All nine actual dependency revisions match the committed manifest.
- All 42 original source and port hashes match the pinned manifest; nine
  files have explicitly recorded compatibility changes.
- An imported false-arithmetic statement `1 = 0` was rejected as expected.
- **NaNoda checked 33,087 declarations with no errors**,
  covering the full exported dependency closure of all 28 selected targets.
  The strict allowlist permits only the three standard axioms above and
  treats any other axiom as a hard error. Target statements were also printed.

The independently implemented checker is NaNoda at commit
`4c544ed4099c8227f07d5de77ad1e69fb0740a27`; the Lean exporter is pinned at
`6cea97789dc088ea47fcea15692db85685aedac5`. Leanchecker reuses Lean's own kernel
and is not a separately implemented checker.

## Reproducible inputs and receipts

Use Lean **4.34.0**, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, and the committed manifest.
[README.md](README.md) gives the fresh-checkout commands.
[UPSTREAM.json](UPSTREAM.json) fixes immutable URLs, original Git blob and
SHA-256 hashes, the exact port edits, and final SHA-256 hashes. The bootstrap
downloads source rather than prebuilt upper-proof objects; pinned Mathlib
cache objects are used.

Our original `JSP000725.lean` is byte-identical to proof revision
`a197ebc6cc3ea878c60db0f2456465cef1e8e09b` and has SHA-256
`a3c0add755c8df4967e688693e7024610965b623d803127abbf72b287f6b1e2a`. The completed endpoint combines that original
construction with our new bridge and the attributed full upper proof.

[Public CI log](verification/public-ci.log) and
[receipt](verification/public-ci-receipt.json) preserve the executed hosted
result. The receipt also records the workflow artifact identifier, size,
API-reported digest and retention date. That digest is reported by GitHub;
we do not represent it as a locally recomputed ZIP digest. The workflow archive
contains tested source, logs, the export and its checker configuration.
Hosted artifacts have finite retention; the committed receipts and decoded
log remain available in the repository.

[Local verification record](verification/verification.json),
[axiom reports](verification/axioms.log), adjacent kernel logs,
[negative control](verification/negative-control.log), and
[local transcript](verification/local-verification.log) preserve the local
results. The local build resumed prior successful, hash-matched compilations;
the hosted run rebuilt every module without that resume option. The local
record's preparation HEAD is the original checkout, not the publishing commit;
the source hashes identify the newly completed files precisely.

This documentation revision adds receipts after the tested proof commit. The
46 source hashes remain unchanged. These automated contributor-run checks
do not constitute independent human review, organizer acceptance, priority
certification or award entitlement.

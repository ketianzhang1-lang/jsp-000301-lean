# JSP-000476: complete square-sum-free extremal bounds

We connect our existing construction classification to the previously public
complete Nguyen–Vu formalization. Our direct endpoint is
`JSP000476.complete_problem` in `JSP000476Complete.lean`.

**The complete integration passed our exact-version checks** at commit
`37d21e1fdb63be5366acafb0fbb1b0b24d85387b`: 446 compilation units, 40 axiom
audits, fresh Lean replay of 91,704 declarations in the theorem dependency
closure, and an independent NaNoda check of 92,532
declarations. See [VERIFICATION.md](VERIFICATION.md) for reproducible evidence
and the separate public CI status.

For every real epsilon > 0, there is a threshold N0 such that, for every N >= N0:

- some square-sum-free subset A of {1,...,N} has cardinality at least N^(1/3-epsilon);
- every square-sum-free subset A of {1,...,N} has cardinality at most N^(1/3+epsilon).

Square-sum-free means that **every nonempty subset** has sum different from every
natural square. The interval consists of positive integers; zero is excluded.
The empty set is admissible. No extra structural hypothesis is placed on A.
The theorem `uniform_polylog_upper_bound` also exposes the uniform Nguyen–Vu bound.

## Reproduce

Use Lean 4.33.0 and the exact dependency revisions in `lake-manifest.json`:

```sh
lake exe cache get Mathlib
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The bootstrap script restores 443 upstream modules from immutable, checksum-checked
sources and applies their existing documented patches, including upstream proof repairs. The verification
script compiles that closure and our files, audits all 40 listed theorem endpoints,
and replays the Lean kernel. The separate script exports the selected endpoints and
checks their transitive proof closure using NaNoda with a strict axiom allowlist.

See [PROVENANCE.md](PROVENANCE.md) for the exact source and contribution breakdown.
Our original `JSP000476.lean` remains unchanged from revision
`4ab28a44e7c89d814699c70f79a0e138f72162e7`. The earlier documentation and receipt are
retained in `PREVIOUS_README.md` and `PREVIOUS_VERIFICATION.md`.

We submit our bridge and integration work as `ketianzhang1-lang`, with OpenAI
ChatGPT assistance. We retain the earlier proof authors' credit; this integration
does not establish first-completion priority or award entitlement.

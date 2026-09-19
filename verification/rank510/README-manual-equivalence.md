# Manual module-build equivalence for JSP-000506 selection

This is a disclosed audit-harness adaptation, not a change to the submitted proof, its Lake configuration, dependency pins or the official audit script.

## Why it is needed and permitted

The selected Lean 4.31 Lake configuration registers roots `JSP000506`, `JSP000506Bridge` and `JSP000506Complete`. Its selection module is instead compiled explicitly by the submitted `scripts/verify_selection.py`. Fixed Lake sources show that `lake build +JSP000506Selection` cannot resolve that unregistered module:

- https://github.com/leanprover/lean4/blob/v4.31.0/src/lake/Lake/CLI/Build.lean
- https://github.com/leanprover/lean4/blob/v4.31.0/src/lake/Lake/Config/LeanLibConfig.lean
- https://github.com/leanprover/lean4/blob/v4.31.0/src/lake/Lake/Config/Module.lean

The official fixed [reproduction reference](https://github.com/TheJustinSunPrize/awards/blob/38e63c424c7196f8d4ceb664c5c25f0c0529d5e2/skills/lean-verify/references/reproduction.md), section 3, permits equivalent manual explicit-module/source checks when the tool's target interface does not fit the project. It requires exact versions, recorded commands, source checks, declaration/axiom checks and disclosed limitations. The skill's automation reference likewise distinguishes CLI limitations from proof failures and does not permit changing proof sources to force compatibility.

## Exact behavior

Only the `506-selection` audit stage supplies this executable through the official script's `--lake` parameter. These two exact argument arrays are intercepted:

```text
build +JSP000506Selection
build +JSP000506.VerificationSelection
```

Each intercepted invocation actually runs the pinned, trusted Lake executable as:

```text
REAL_LAKE env lean -DwarningAsError=true -j1 -M12000 -o OUTPUT SOURCE
```

The source and output paths are derived from a fixed two-module allowlist. The original selection source or auditor bridge is freshly compiled on **every** invocation. Its pre-existing output is removed first; no cache-success shortcut exists. Compiler stdout/stderr is streamed to the official audit log and also saved in a per-invocation log. Nonzero compiler status is propagated. Source hashes before and after, real argv, cwd, output log/hash, generated artifact hash, duration and exit code are appended to `/out/manual-module-builds.jsonl`.

All other invocations, including tool-version queries, source-file checks and the generated `#check` / full `#print` / `#print axioms` files, use `os.execv` to run the real pinned Lake unchanged. The adapter is copied from the read-only harness to the evidence directory with executable permission; `/out/manual-equivalence.json` records its hash, real Lake path and scope.

The original complete verifier, original module compilation, original kernel replay, added bridge replay and independent exporter/checker stages still call the real pinned Lake directly. The main 506 version and every other project do not use this adapter.

## Limits and reporting

The two intercepted build operations are explicit Lean source compilations under the original Lake environment, **not** native Lake module-target builds. Reports must identify that manual equivalence. The original proof is unchanged, and the original verifier must succeed first. Any compiler error remains an audit failure; semantic correspondence and whole-problem coverage are separate review judgments.

The official audit implementation remains byte-for-byte unchanged. Its normal source checks and transitive axiom inspection still run for every target; its use with this declared adapter must not be described as an unadapted official command. Protocol tests of this adapter, if run, use a fake compiler executable solely to test routing and failure propagation and are not Lean verification evidence.

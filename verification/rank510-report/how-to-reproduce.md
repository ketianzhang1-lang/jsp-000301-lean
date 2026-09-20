# Reproducing the rank-five-through-ten audit

This guide describes the pinned harness and its checks. It does not assert a successful result. Read the finalized report for actual outcomes and any later explicitly identified correction run.

## Fixed inputs

- Harness repository: `https://github.com/ketianzhang1-lang/jsp-000301-lean`.
- Select each exact harness, workflow run and job from `final-metadata.json → jobs → <group>` accompanying the finalized report. Groups may use different correction runs; a whole workflow's conclusion is not the result of every group.
- Harness directory: `verification/rank510`.
- Workflow: `.github/workflows/lean-verify-rank510.yml`.
- Official rules/skill commit: `38e63c424c7196f8d4ceb664c5c25f0c0529d5e2` in `TheJustinSunPrize/awards`.
- Initial eight-group run: [35476644569](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35476644569). Its failed 393, 728, 636, 585 and both 506 attempts remain part of the history. Select successful exact-version jobs individually from final metadata rather than inferring an overall success.
- The first corrected 393 attempt [35477117193](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35477117193) selected proof `aa1ed1bac2eb0c1ec33723ff802ff3b9b6c02ee8`.
- The 393 first-correction attempt completed the selected proof's full original verifier and explicit upstream kernel replay, then failed only in the auditor bridge (complex minimum 0/1 simplification and an unnecessary-simpa warning). Preserve this second failure artifact. The final 393 job must come from final metadata; its proof commit remains unchanged.
- Corrected 728 run: [35477208711](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35477208711); only manifest identifiers and requirement references changed.
- Corrected 636/585 run: [35477834039](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35477834039), harness `12fb870e5c449902bf7085c00684b606ac06fa5d`. Their proof commits remain unchanged. The finalized per-job metadata controls the ultimate evidence selection.
- Later 393/728 correction run: [35479808961](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35479808961), harness `3195910470b2fcd7712bd983c241d624937321d5`. It fixes the 393 auditor bridge and 728's verification-entry routing; both selected proof commits remain unchanged. The 393 bridge file SHA-256 is `d35b577311e7b2302fb6759b7ee1a4fc404938ae713ffe770f9e73196f1e0ad4`.
- Corrected 506 main/selection run: [35479940510](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35479940510), harness `1e52e4f5851d9751ddc637d383e365047b749fad`. It corrects the shared auditor bridge's elaboration using an explicit `Tendsto` target; both submitted proof versions and target manifests remain unchanged.
- Eight group keys: `636`, `912-full`, `912-modular`, `393-general`, `728`, `585`, `506-main`, `506-selection`.

The `config.json` in that harness supplies every selected proof SHA, branch, project path, toolchain, bootstrap command and original verifier. Do not replace an exact commit with a current branch tip. A separate full-history proof clone is needed for each group; in particular, the selection verifier reads its older base commit using `git show`.

| Key | Original verification command, in configured project directory | Expected original scope | Fresh target entries |
|---|---|---|---:|
| 636 | `bash scripts/verify.sh` | 79 original targets; 8 proof modules | 82 |
| 912-full | `bash scripts/verify.sh` | Both source layouts, 7 target closures per layout; fresh standalone audit/export | 9 |
| 912-modular | Same | Same original reproduction; separate modular audit/export | 9 |
| 393-general | `python3 scripts/verify_general.py` | 27 compiled source modules; 13 retained + 11 new original target closures | 29 |
| 728 | `bash scripts/verify.sh` | 47 compiled source modules; 27 original target closures | 35 |
| 585 | `bash scripts/verify.sh` | 66 compiled source modules; 61 original target closures | 65 |
| 506-main | `bash scripts/verify.sh` | 5 compiled units including the single 480-module upstream closure; 49 original targets | 55 |
| 506-selection | `python3 scripts/verify_selection.py` | Full base reproduction plus selection source, 60-target audit and replay | 68 |

The total is 352 group-specific entries. The two 912 layouts deliberately define the same theorem names; never import them together in one process. One 506 version's successful check does not certify the other.

## Isolated reproduction of one group

Use a disposable Linux machine with Docker, Git, Python 3 and sufficient disk/memory. The reference workflow uses Ubuntu 24.04, four CPUs per container, 14 GiB memory and 24 GiB combined memory/swap, with 16 GiB host swap provisioned for the large proof. If these resources are unavailable, record a resource limitation rather than treating an interrupted check as a mathematical failure.

The commands below are an alternative way to run the same pinned harness. They keep network access during preparation and disable it for submitted proof execution. They do not mount credentials or a personal home directory.

Choose exactly one of the eight keys. Point `AUDIT_METADATA` at the final metadata file distributed with the finalized report, then create a new working directory. The metadata selects the actual successful job for that group; do not substitute a guessed run or the initial harness.

```bash
set -euo pipefail
AUDIT_KEY=636
AUDIT_METADATA=/absolute/path/to/final-metadata.json
AUDIT_HARNESS_SHA=$(python3 -c 'import json,re,sys; m=json.load(open(sys.argv[1])); h=m["jobs"][sys.argv[2]]["harness_commit"]; assert re.fullmatch("[0-9a-f]{40}",h); print(h)' "$AUDIT_METADATA" "$AUDIT_KEY")
AUDIT_WORK=$(mktemp -d -t lean-rank510-reproduce-XXXXXXXX)
cd "$AUDIT_WORK"

git clone --no-checkout https://github.com/ketianzhang1-lang/jsp-000301-lean.git harness-repo
git -C harness-repo checkout --detach "$AUDIT_HARNESS_SHA"
cp -a harness-repo/verification/rank510 harness

git clone --no-checkout https://github.com/ketianzhang1-lang/jsp-000301-lean.git proof
AUDIT_PROOF_SHA=$(python3 -c 'import json,sys; print(json.load(open("harness/config.json"))[sys.argv[1]]["commit"])' "$AUDIT_KEY")
AUDIT_PROOF_BRANCH=$(python3 -c 'import json,sys; print(json.load(open("harness/config.json"))[sys.argv[1]]["branch"])' "$AUDIT_KEY")
AUDIT_LEAN_VERSION=$(python3 -c 'import json,sys; print(json.load(open("harness/config.json"))[sys.argv[1]]["lean_version"])' "$AUDIT_KEY")
git -C proof checkout --detach "$AUDIT_PROOF_SHA"
git -C proof merge-base --is-ancestor "$AUDIT_PROOF_SHA" "origin/$AUDIT_PROOF_BRANCH"

mkdir evidence
git -C proof rev-parse HEAD > evidence/SOURCE_COMMIT
git -C proof rev-parse "origin/$AUDIT_PROOF_BRANCH" > evidence/BRANCH_TIP

git clone --no-checkout https://github.com/TheJustinSunPrize/awards.git official
git -C official checkout --detach 38e63c424c7196f8d4ceb664c5c25f0c0529d5e2
cp official/skills/lean-verify/scripts/audit.py harness/audit.py
cp -a official/skills/lean-verify evidence/official-skill
cp -a harness evidence/harness

docker build --build-arg LEAN_VERSION="$AUDIT_LEAN_VERSION" -t lean-rank510-audit harness
docker image inspect lean-rank510-audit > evidence/image-inspect.json
sudo chown -R 10001:10001 proof evidence
```

Prepare pinned dependencies and compatible external checkers:

```bash
docker run --rm --cap-drop ALL --security-opt no-new-privileges \
  --cpus 4 --memory 14g --memory-swap 24g --pids-limit 1024 \
  --user 10001:10001 -e CARGO_HOME=/out/cargo-cache \
  -v "$PWD/proof:/work" -v "$PWD/harness:/harness:ro" \
  -v "$PWD/evidence:/out" \
  lean-rank510-audit python3 /harness/runner.py prepare "$AUDIT_KEY"
```

Run the three offline stages in order, stopping if any stage fails:

```bash
for AUDIT_STAGE in original audit replay; do
  docker run --rm --network none --cap-drop ALL --security-opt no-new-privileges \
    --cpus 4 --memory 14g --memory-swap 24g --pids-limit 1024 \
    --user 10001:10001 -e CARGO_HOME=/out/cargo-cache \
    -v "$PWD/proof:/work" -v "$PWD/harness:/harness:ro" \
    -v "$PWD/evidence:/out" -v "$PWD/evidence/tools:/out/tools:ro" \
    lean-rank510-audit python3 /harness/runner.py "$AUDIT_STAGE" "$AUDIT_KEY" || exit "$?"
done
```

The original stage removes project build outputs before invoking the unmodified submitted verifier. It does not use `--resume`. The audit stage adds only the auditor bridge to the disposable proof tree, fixes the target manifest's runtime root, performs official preflight, and checks every listed target. The corrected 636/585 harness first compiles its bridge with the real pinned compiler under warnings-as-errors; this stops immediately on a bad bridge and does not replace any official target check. The replay stage checks the bridge, exports every target's full dependency closure, runs NaNoda with a hard-error axiom allowlist, rechecks all nine dependency SHAs, compares source hashes and records final source state.

Do not interpret the shell loop's completion as success. Check all stage exit records and the full logs, including whether later stages were skipped. Repeat from a fresh directory for each remaining group. The 393 general proof uses the repository root as its project, unlike the project subdirectories of the other submissions.

## Explicit adaptations

### Exporter toolchain

For Lean 4.34 projects, exporter source `6cea97789dc088ea47fcea15692db85685aedac5` originally specifies **4.35.0-rc2**. The harness changes only the disposable exporter's `lean-toolchain` file to the selected proof project's 4.34.0 file, then builds the exporter. This is a compatibility rebuild of fixed exporter source, not an upstream exporter release natively pinned to 4.34.0. Preserve its build log, compiler version, source revision and export command.

For the 506 projects, exporter source `8554815c2dc6b7abe99ec1f08849c9759ba77947` natively specifies 4.31.0. NaNoda source `4c544ed4099c8227f07d5de77ad1e69fb0740a27` is used for every group, with `cargo build --release --locked`.

No submitted proof toolchain, manifest or proof source is upgraded to make a checker work.

### 506 selection module

The original Lake roots do not register `JSP000506Selection`. Its original verifier therefore compiles that source directly. The official audit runner is unmodified but uses an explicitly disclosed `--lake` adapter for this one group.

Only these two commands are translated to fresh explicit compilation with the pinned real Lake:

```text
build +JSP000506Selection
build +JSP000506.VerificationSelection
```

The replacement is `REAL_LAKE env lean -DwarningAsError=true -j1 -M12000 -o OUTPUT SOURCE`. The output is deleted before every compilation, failure status is preserved and source/output hashes plus full command logs are recorded. All other argv are executed by the real Lake unchanged. See [README-manual-equivalence.md](harness/README-manual-equivalence.md). Read `manual-equivalence.json`, `manual-module-builds.jsonl` and the referenced logs; do not describe these as native Lake module-target builds.

### 636/585 auditor corrections

The initial 636 original verifier and all 79 original target checks succeeded, while the three auditor bridge checks failed because the proposed `profile_eq` proof used `rfl` for an equality that was not definitionally reducible. The corrected bridge unfolds the two profiles and proves the relevant components by congruence; the submitted proof is unchanged.

The initial 585 complete verifier and its 61 original axiom closures succeeded. The new audit then exposed a bridge record-syntax error and attempted native Lake builds for 11 declarations from an unregistered definition module. The corrected bridge fixes the record construction and supplies the needed `Nonempty` instance. Targets `t37`–`t47` retain their exact declarations and use tracked configured `AuditComplete.lean` as the verification entry. Their actual tracked definition file `JSP000585Bridge.lean` and its SHA-256 remain explicit in each manifest record. The unchanged original verifier compiles and kernel-replays that definition module. The importing entry does not become its definition file.

The corrected harness adds a strict explicit bridge precompile before the official audit. This uses the actual fixed Lean compiler, emits a real module artifact, and fails on warnings; every original verifier and official target operation still runs. Preserve both failed first-attempt artifacts and select the corrected jobs independently.

### 393/728 subsequent auditor corrections

The first corrected-proof 393 attempt completed its full original verifier and explicit upstream kernel replay, but its auditor bridge failed at the literal complex minimum's zero/one boundary and an unnecessary-simpa warning. The later bridge uses explicit polynomial-support rewrites and exact theorem application, retaining the five original independent bridge statements. This correction changes no submitted proof source.

The first corrected-ID 728 attempt passed all eight new auditor bridge targets. Its audit failed on eight existing declarations defined in `JSP000728Bridge.lean`, because that module is not a registered native Lake target. The later manifest routes `t017`–`t024` through the tracked configured importing module `JSP000728Complete`. Each target preserves its actual definition path `JSP000728Bridge.lean` and SHA-256 `f5c0d3997678f9443f197ad1693ce0ea72f62798e0ed6c5845f676ea69eb9ada`. The original verifier compiles and kernel-replays that definition module. This is an entry-routing correction, with the proof, the eight auditor bridges and all 35 declaration names unchanged.

### 506 auditor elaboration correction

Both initial 506 jobs completed their clean original verifiers and every original target's official audit (49 main and 60 selection declarations). Their new auditor bridges shared a failure in the divergence conclusion's elaboration. The corrected bridges explicitly state the intended `Tendsto` target before applying the submitted theorem. All original proofs, the additional selection assumptions, and both target manifests remain unchanged. Preserve both failed attempts; the later main and selection jobs must each succeed independently.

### Fetched declaration sources

Some original targets are exposed through a tracked importing/audit entry to satisfy provenance checks for the selected submitting-repository commit. Their real definitions remain in separately identified, hash-pinned bootstrap files. Read `definition_source`, `UPSTREAM.json`, bootstrap logs and original source build logs together. The importing entry is not itself the definition file. The actual upstream source must have been compiled in the clean original verifier and included in kernel/exported dependency checks.

## Evidence review

For each group, retain and inspect:

1. Exact HEAD and branch ancestry, actual tool versions, resolved image metadata and all nine dependency revisions.
2. `tracked-before-prepare.json`, `tracked-after-prepare.json`, `source-before.json` and `source-after.json`; original/ported bootstrap hashes; final Git status.
3. `original-clean-verifier.log/.json`, `original-completion.json`, and `fresh-project-evidence/` plus any `fresh-extra-*/`. Read build/module counts and every control failure's actual error, rather than trusting a label.
4. `targets.json`, `preflight/`, `audit/`, `official-audit.log/.json`, every target's full statement and axiom result. Expected totals are in the table above.
5. Original kernel logs, the explicit additional 393 replay, `bridge-kernel.log/.json`, `export-command.json`, `export-stderr.log`, `export.ndjson.gz`, NaNoda config, statements and success/error output.
6. `mechanical-completion.json` only if all prior stages succeeded; semantic verdicts still require the six reviews. Standard axioms are only `propext`, `Classical.choice`, `Quot.sound`.
7. For 506-selection, the adapter's per-invocation journal and exact executable hash.

A native computation dependency, an unexpected axiom, a failed theorem command, a malformed/missing axiom output, an input change, a timeout or a resource exhaustion must remain visible. Their implications differ; do not replace a failed selected commit with a modified proof without identifying the new version.

## Artifact integrity

The hosted workflow writes `SHA256SUMS.json` for each artifact, including logs and source snapshots. After downloading and safely extracting one artifact, set its actual directory below and verify every listed file:

```bash
python3 - /absolute/path/to/extracted-artifact <<'PY'
import hashlib, json, pathlib, sys
root = pathlib.Path(sys.argv[1]).resolve()
manifest = json.loads((root / "SHA256SUMS.json").read_text())
for relative, expected in manifest.items():
    path = (root / relative).resolve()
    if root not in path.parents:
        raise SystemExit("Unsafe artifact path: " + relative)
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit("Hash mismatch: " + relative)
print("All", len(manifest), "listed artifact file hashes match.")
PY
```

Independently compare the downloaded archive digest against the hosting metadata as well. Successful hashes show byte integrity, not a successful proof; inspect the contents and per-target counts. Keep exported raw logs even if a workflow failed.

## Interpretation and later changes

The initial 393 candidate `ed82d0cb2d35fca55f32b00cb75bdd5271226eb8` failed only an unused `[CharZero K]` section-assumption warning under warnings-as-errors. The selected correction `aa1ed1bac2eb0c1ec33723ff802ff3b9b6c02ee8` explicitly omits that unused assumption; it does not disable a linter or change the mathematical argument. Preserve the failed artifact and verify the new commit independently.

The initial 728 original verifier completed its 47-module run before official preflight rejected target IDs containing periods. The corrected manifest uses `t000`–`t034` and synchronized requirement references, with the proof and declarations unchanged. Preserve the initial failure and select the corrected 728 run independently. The official loader's successful Python schema check is not a Lean-verification result.

Preserve the second failed 393 and 728 artifacts as well. Successful original verification or successful individual bridge targets in those attempts do not replace a full successful check of the final audit inputs.

The final report must state the four judgments separately for each submission and identify both 912 layouts and both 506 proof versions. In 393, the rational-only historical commit remains a limited-domain result; only the new general-coefficient commit may establish the corrected original scope after its own successful checks.

An audit uses the fixed rules revision listed above. Before claiming compliance with the latest requirements, reread official main and compare relevant templates, CONTRIBUTING and lean-verify references if it changed. Recheck the awards PR heads, selected proof references and merged status. A changed live head does not retroactively change what the pinned run checked.

These checks do not establish solver registration, completed identity verification, maintainer acceptance, a merged PR or award entitlement. A retrospective check cannot satisfy a literally earlier timestamp by backdating it.

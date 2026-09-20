# Reproduce exact-version Lean verification

The final selected jobs below come from final-metadata.json; do not substitute the latest branch tip.

These instructions distinguish three tasks: review already saved raw evidence, rerun the strict archive/evidence inspector, and freshly execute a selected proof in an isolated container. None of these tasks alone decides natural-language correspondence, mathematical completeness, attribution, priority or organizer eligibility.

| Group | Proof project | Selected proof commit | Original + bridges | Pinned job and harness |
|---|---|---|---|---|
| 301 | . | `e1a17b0d6728b9d4929d1d4abd3721a27377369a` | 8 + 3 = 11 | [job 106008713557](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35484654492/job/106008713557); [harness `784e798f90142e91aecbf3500e84e25f51a4ba84`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/784e798f90142e91aecbf3500e84e25f51a4ba84/verification/rank1120) |
| 897 | projects/jsp-000897 | `914c6fa28200985d6409b5b34588b9f5c4a87d00` | 8 + 4 = 12 | [job 106008713536](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35484654492/job/106008713536); [harness `784e798f90142e91aecbf3500e84e25f51a4ba84`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/784e798f90142e91aecbf3500e84e25f51a4ba84/verification/rank1120) |
| 907 | projects/jsp-000907 | `555ce4f13bf7e8e8557020728f7f97ad3d1f51e0` | 35 + 5 = 40 | [job 106011977016](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35485853057/job/106011977016); [harness `31b2395743695fee2be30dae3ba006b4b240e5be`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/31b2395743695fee2be30dae3ba006b4b240e5be/verification/rank1120) |
| 465 | projects/jsp-000465 | `6a793b157c1afdf29f3e6bbbf3cf514535d1dfca` | 7 + 6 = 13 | [job 106010114425](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35485174811/job/106010114425); [harness `7c5551ac6a716eb73cfd599575358883e6549b75`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/7c5551ac6a716eb73cfd599575358883e6549b75/verification/rank1120) |
| 388 | projects/jsp-000388 | `a9eae7a01edade3d5d9a386144dcd2848b4de917` | 18 + 5 = 23 | [job 106010114390](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35485174811/job/106010114390); [harness `7c5551ac6a716eb73cfd599575358883e6549b75`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/7c5551ac6a716eb73cfd599575358883e6549b75/verification/rank1120) |
| 140 | projects/jsp-000140 | `724a733a2b498d7b3b956e66b76d7334cc906eaf` | 46 + 9 = 55 | [job 106010114343](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35485174811/job/106010114343); [harness `7c5551ac6a716eb73cfd599575358883e6549b75`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/7c5551ac6a716eb73cfd599575358883e6549b75/verification/rank1120) |
| 725 | projects/jsp-000725 | `d0d37952bba030d7c8a68f000094e0d601d9fed7` | 28 + 6 = 34 | [job 106008713611](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35484654492/job/106008713611); [harness `784e798f90142e91aecbf3500e84e25f51a4ba84`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/784e798f90142e91aecbf3500e84e25f51a4ba84/verification/rank1120) |
| 554 | projects/jsp-000554 | `21fcf006fd68b0bead9f979b704c92032f05cba8` | 37 + 7 = 44 | [job 106011976984](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35485853057/job/106011976984); [harness `31b2395743695fee2be30dae3ba006b4b240e5be`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/31b2395743695fee2be30dae3ba006b4b240e5be/verification/rank1120) |
| 746 | projects/jsp-000746-sharp | `4dfb40abe0cd1e538bbfccb1cc50f4829fb7383a` | 8 + 4 = 12 | [job 106011976943](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35485853057/job/106011976943); [harness `31b2395743695fee2be30dae3ba006b4b240e5be`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/31b2395743695fee2be30dae3ba006b4b240e5be/verification/rank1120) |
| 1021 | projects/jsp-001021 | `7642a7f5eb190da6319b6ae7f11c829d7737e2dd` | 11 + 6 = 17 | [job 106015067112](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35486985097/job/106015067112); [harness `d5631f8e784961d2afe6fe24830be3dd06aaf955`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/d5631f8e784961d2afe6fe24830be3dd06aaf955/verification/rank1120) |
| 465-uniform | projects/jsp-000465 | `78dbc684a1ce3d392b150d98bdc5b94a9269f3e3` | 12 + 9 = 21 | [job 106010114318](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35485174811/job/106010114318); [harness `7c5551ac6a716eb73cfd599575358883e6549b75`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/7c5551ac6a716eb73cfd599575358883e6549b75/verification/rank1120) |
| 897-stability | projects/jsp-000897 | `4d15dc035f56658776c01729216f99b776a5ad35` | 15 + 6 = 21 | [job 106009440085](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35484922308/job/106009440085); [harness `2eff10da34032979ab2b5d8ec2f69e0915406ee5`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/2eff10da34032979ab2b5d8ec2f69e0915406ee5/verification/rank1120) |

## Review saved evidence and recover original archive identity

The curated delivery contains the complete extracted successful and failed raw evidence, immutable file-hash inventories and external artifact receipts. It intentionally omits duplicate original GitHub artifact ZIP downloads. Do not reconstruct those originals by recompressing the raw files: ZIP metadata, compression and ordering affect their byte identity.

Before running `inspect_evidence.py` or `finalize_report.py --check-only`, obtain each selected group’s **original artifact ZIP** using its `evidence/GROUP/artifact-receipt.json` fields `workflow_run`, `artifact_id` and `filename`. Save it as `evidence/GROUP/FILENAME` beside that receipt. Match both `sha256` and `bytes`. The GitHub artifact URL is `https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/WORKFLOW_RUN/artifacts/ARTIFACT_ID`; its API download endpoint is `https://api.github.com/repos/ketianzhang1-lang/jsp-000301-lean/actions/artifacts/ARTIFACT_ID/zip`. Use your own authorized GitHub session or download client when authentication is required; credentials are never mounted into proof containers.

The workflow requests **90-day artifact retention**, and these receipts were created on 2026-09-20; GitHub may remove an artifact earlier. If its original archive is no longer available, the preserved extracted logs and their hashes remain reviewable, but the original archive-identity gate cannot be rerun from the curated bundle alone. This is an evidence-availability limit, not a reason to weaken the strict inspector.

The complete finalizer also validates retained failed-attempt archives, so recover their original ZIPs from their own receipts as well. Inspecting only successful selected groups requires their successful archives. Failed attempts are historical evidence and never count as successful execution.

Verify downloaded byte identity from the delivery root without executing proof code:

```python
import hashlib, json
from pathlib import Path
for receipt_path in sorted(Path("evidence").glob("*/artifact-receipt.json")):
    receipt = json.loads(receipt_path.read_text())
    archive = receipt_path.parent / receipt["filename"]
    if not archive.is_file():
        print("Original ZIP not supplied:", receipt_path.parent.name)
        continue
    assert archive.stat().st_size == receipt["bytes"]
    h = hashlib.sha256()
    with archive.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    assert h.hexdigest() == receipt["sha256"]
    print("Original ZIP identity matched:", receipt_path.parent.name)
```

The inspector reads raw evidence and does not run Lean:

```bash
python3 inspect_evidence.py --output evidence/reinspection-summary.json
python3 finalize_report.py --check-only
```

Use repeated `--key` flags, for example `--key 301 --key 897`, when only those groups’ original archives have been recovered. Do not overwrite the canonical execution summary merely to turn a missing-archive result into a pass. The strict finalizer also needs final metadata, selected.json, the published documentation-repair receipts and all ten reviewed scope records.

## Fresh execution in a disposable verification environment

Prerequisites: Git, Python 3, Bash, Docker and sufficient disk/memory. The recorded GitHub runner uses Ubuntu 24.04, four container CPUs, a 14 GiB memory limit, 24 GiB memory-plus-swap limit, 1,024 processes and an additional 16 GiB host swap allocation. The selected workflow describes that resource setup. Do not run untrusted Lean or Lake commands directly on a credential-bearing host. Preparation downloads pinned dependencies; original build, target audit and replay/checker stages use `--network none`, UID/GID 10001, all capabilities dropped and `no-new-privileges`. Only the disposable proof checkout and evidence directory are writable; harness and checker-tool mounts are read-only during checking.

The recipe below selects `301` as a concrete example. Change only `audit_group` to another row key. Start in the delivery root after final metadata exists; use a fresh working directory for every execution. The selected harness is specific to that group’s actual final job, and can differ from another group’s harness commit. The commands do not claim a new run has the byte identity or timestamp of the historical GitHub job.

```bash
set -euo pipefail
audit_group=301
selected_harness=$(python3 -c 'import json,sys; print(json.load(open("final-metadata.json"))["jobs"][sys.argv[1]]["harness_commit"])' "$audit_group")
mkdir "reproduction-$audit_group"
cd "reproduction-$audit_group"
git clone --no-checkout https://github.com/ketianzhang1-lang/jsp-000301-lean.git harness-repo
git -C harness-repo checkout --detach "$selected_harness"
cp -a harness-repo/verification/rank1120 harness
mkdir evidence
proof_sha=$(python3 -c 'import json,sys; print(json.load(open("harness/config.json"))[sys.argv[1]]["commit"])' "$audit_group")
proof_branch=$(python3 -c 'import json,sys; print(json.load(open("harness/config.json"))[sys.argv[1]]["branch"])' "$audit_group")
git clone --no-checkout https://github.com/ketianzhang1-lang/jsp-000301-lean.git proof
git -C proof checkout --detach "$proof_sha"
git -C proof merge-base --is-ancestor "$proof_sha" "origin/$proof_branch"
git -C proof rev-parse HEAD > evidence/SOURCE_COMMIT
git -C proof rev-parse "origin/$proof_branch" > evidence/BRANCH_TIP
git clone --no-checkout https://github.com/TheJustinSunPrize/awards.git official
git -C official checkout --detach 38e63c424c7196f8d4ceb664c5c25f0c0529d5e2
cp official/skills/lean-verify/scripts/audit.py harness/audit.py
printf '%s  %s\n' '5db45dddcb4d588bc27e7c7161fbca5cedaa3e73e1c40843d21f5a214323cd07' 'harness/audit.py' | sha256sum --check
git -C official rev-parse HEAD > evidence/OFFICIAL_RULES_COMMIT
printf '%s\n' "$selected_harness" > evidence/HARNESS_COMMIT
cp harness-repo/.github/workflows/lean-verify-rank1120.yml evidence/workflow.yml
cp -a official/skills/lean-verify evidence/official-skill
cp -a harness evidence/harness
lean_version=$(python3 -c 'import json,sys; print(json.load(open("harness/config.json"))[sys.argv[1]]["lean_version"])' "$audit_group")
docker build --build-arg LEAN_VERSION="$lean_version" -t lean-rank1120-repro harness
docker image inspect lean-rank1120-repro > evidence/image-inspect.json
sudo chown -R 10001:10001 proof evidence
common=(--rm --cap-drop ALL --security-opt no-new-privileges --cpus 4 --memory 14g --memory-swap 24g --pids-limit 1024 --user 10001:10001 -e CARGO_HOME=/out/cargo-cache -v "$PWD/proof:/work" -v "$PWD/harness:/harness:ro" -v "$PWD/evidence:/out")
docker run "${common[@]}" lean-rank1120-repro python3 /harness/runner.py prepare "$audit_group"
for audit_stage in original audit replay; do
  docker run "${common[@]}" --network none -v "$PWD/evidence/tools:/out/tools:ro" lean-rank1120-repro python3 /harness/runner.py "$audit_stage" "$audit_group"
done
```

A rerun’s dependency downloads, image identity, versions, durations and output hashes must be recorded independently. The Docker base tag is specified in the selected Dockerfile; the historical image ID is evidence for that run and does not imply a future rebuild has byte-identical operating-system packages. Never attach a historical artifact receipt to a newly produced ZIP.

## What each stage must establish

1. **Prepare:** read exact toolchain and lockfile, bootstrap only hash-pinned upstream sources where configured, prepare Mathlib, and build the pinned exporter and independent checker. The selected proof commit, actual branch containment, every dependency revision and source/configuration bytes are recorded. Full Git history is needed for both supplements’ byte comparison with their base commits.

2. **Original:** remove the project build directory and stale evidence outputs, then execute the selected original verifier without resume. Recompile the full reused dependency closure and local modules, perform original kernel replays, audit every original target, and reject the false arithmetic negative control. Restore only tracked historical evidence after copying the fresh logs; compare source/configuration inputs before and after.

3. **Audit:** place the separately identified auditor bridge under the configured library, strict-compile it with warnings as errors, then invoke the **unchanged** official audit script on the group’s manifest. Its preflight pins the tracked theorem entries; each target gets explicit module build, source check, `#check`, `#print`, and `#print axioms`. Downloaded definition sources and tracked import entries are separately identified in the target index and checked by source hashes.

4. **Replay:** replay the bridge module with the pinned Lean kernel checker; export all listed original and bridge target closures; run NaNoda with hard rejection of any axiom outside `propext`, `Classical.choice`, and `Quot.sound`. Preserve nonempty printed statements, success output, export hash, actual dependency revisions, final source hashes and negative-control evidence. A target can use a subset of those standard foundations.

The official rules and skill are pinned to [awards 38e63c424c7196f8d4ceb664c5c25f0c0529d5e2](https://github.com/TheJustinSunPrize/awards/tree/38e63c424c7196f8d4ceb664c5c25f0c0529d5e2/skills/lean-verify). The unchanged `audit.py` SHA256 is `5db45dddcb4d588bc27e7c7161fbca5cedaa3e73e1c40843d21f5a214323cd07`. The automatic script does not itself determine semantic completeness. Final source-to-statement judgment, original quantifiers, all cases and attribution are separately reviewed.

## Explicit compatibility and module-routing disclosures

All twelve groups use Lean 4.34.0. `lean4export` source commit `6cea97789dc088ea47fcea15692db85685aedac5` originally targets Lean 4.35.0-rc2; the recorded preparation copies the project’s exact 4.34.0 toolchain pin into the exporter checkout and rebuilds that source. This is a disclosed compatibility rebuild, not a claimed native 4.34 exporter release. NaNoda source is `4c544ed4099c8227f07d5de77ad1e69fb0740a27`, built with Rust 1.90.0 and Cargo `--locked`. Neither source pin authorizes changing a proof’s toolchain or dependencies.

JSP-000301’s selected historical proof commit has no strict Python verification script. [301-original.py](harness/301-original.py) is explicitly auditor-owned: it builds and strict-checks the unchanged original module, replays it, audits all eight public declarations, verifies actual dependency revisions and rejects `1=0`. The later historical strict-verification commit is separate evidence and is never substituted for the selected proof version.

Only two native Lake target forms are missing in selected supplement configurations. Their adapters intercept exactly the calls below. Each intercepted call deletes stale output and invokes the **real pinned Lake** to execute `lean -DwarningAsError=true -j1 -M12000 -o OLEAN SOURCE`; all other argument lists pass to the real Lake unchanged. The original proof, lakefile and official audit script remain unchanged. This is manual-equivalent explicit module compilation, not native Lake-target success.

| Group | Only intercepted command | Actual source | Expected target-audit compilations | Adapter evidence |
|---|---|---|---|---|
| 465-uniform | `lake build +JSP000465Uniform` | `JSP000465Uniform.lean` | 5 | [adapter](harness/465-uniform-manual-lake-adapter.py); `manual-module-builds.jsonl`, compiler logs and `manual-equivalence.json` |
| 897-stability | `lake build +JSP000897Stability` | `JSP000897Stability.lean` | 7 | [adapter](harness/897-stability-manual-lake-adapter.py); `manual-module-builds.jsonl`, compiler logs and `manual-equivalence.json` |

The counts above follow the original target declarations requiring each omitted module. Actual successful compilations, stable source hashes, exact commands, unique logs, output hashes and exit codes must be checked in each final raw artifact; adapter existence or an expected count is not execution evidence. Both supplements also rerun their complete base proofs.

## Evidence coordinates and interpretation

For a selected group, `evidence/GROUP/remote/` holds its immutable extracted artifact; `evidence/GROUP/artifact-receipt.json` is the external ZIP receipt. Key records include `targets.json`, `audit/result.json`, `preflight/`, `original-clean-verifier.json`, `fresh-project-evidence/`, any `fresh-extra-1/`, `bridge-precheck.json`, `bridge-kernel.json`, `export-command.json`, `export.ndjson.gz`, `nanoda-config.json`, `nanoda-statements.txt`, `independent-nanoda.log`, `source-before.json`, `source-after.json` and `SHA256SUMS.json`. Exact group-specific locations are defined by config inspection records; a missing expected log is a failure of evidence, not an empty axiom set.

A finished GitHub job or parser exit code alone does not certify a complete original mathematical solution. Preserve failed attempts, distinguish infrastructure and auditor-only corrections from selected proof changes, and report the actual final level of assurance. This self-check does not establish pre-opening historical timing, solver-candidate registration, merge, identity confirmation, priority or an award.

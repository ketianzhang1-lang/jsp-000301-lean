#!/usr/bin/env python3
"""Generate scope/target and reproduction indexes without executing any Lean code.

Before final-metadata.json exists the documents explicitly leave job selection
pending. Run again after final metadata is fixed to pin every group's harness
and job. No source, raw evidence, metadata, or verification result is changed.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

ROOT=Path(__file__).resolve().parent
REPO='https://github.com/ketianzhang1-lang/jsp-000301-lean'
AWARDS='https://github.com/TheJustinSunPrize/awards'
RULES='38e63c424c7196f8d4ceb664c5c25f0c0529d5e2'
AUDIT_SHA='5db45dddcb4d588bc27e7c7161fbca5cedaa3e73e1c40843d21f5a214323cd07'

def read_json(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(data): return hashlib.sha256(data).hexdigest()
def cell(s): return str(s).replace('|','\\|').replace('\n',' ')
def table(head,rows):
    return '\n'.join(['| '+' | '.join(map(cell,head))+' |','|'+'|'.join('---' for _ in head)+'|']+['| '+' | '.join(map(cell,r))+' |' for r in rows])
def relative(path):
    p=PurePosixPath(path)
    if p.is_absolute() or '..' in p.parts:raise ValueError('Unsafe project-relative path')
    return p

def git_bytes(worktree,commit,path):
    out=subprocess.run(['git','-C',str(worktree),'show',commit+':'+path],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    return out.stdout if out.returncode==0 else None

def proof_path(cfg,path):
    relative(path)
    return path if cfg['project']=='.' else str(PurePosixPath(cfg['project'])/path)

def blob(cfg,path,label=None):
    return f"[{label or path}]({REPO}/blob/{cfg['commit']}/{proof_path(cfg,path)})"

def job_link(meta,key):
    if meta is None:return 'Final job/harness selection pending'
    job=meta['jobs'][key]
    return f"[job {job['job_id']}]({REPO}/actions/runs/{job['run_id']}/job/{job['job_id']}); [harness `{job['harness_commit']}`]({REPO}/tree/{job['harness_commit']}/verification/rank1120)"

def upstream_items(data):
    if isinstance(data,list):return [x for x in data if isinstance(x,dict)]
    if isinstance(data,dict):
        out=[]
        if 'path' in data:out.append(data)
        for value in data.values():
            if isinstance(value,(list,dict)):out.extend(upstream_items(value))
        return out
    return []

def definition(base,key,cfg,target):
    if target['role']=='bridge':
        p=base/'harness'/cfg['bridge_file']
        return f"[auditor `{cfg['bridge_file']}`](harness/{cfg['bridge_file']})",sha(p.read_bytes()),'Auditor input, outside selected proof commit'
    actual=target.get('definition_source',target['source']);path=proof_path(cfg,actual)
    worktree=base/'sources'/cfg.get('source_key',key)
    raw=git_bytes(worktree,cfg['commit'],path)
    expected=target.get('definition_sha256')
    if raw is not None:
        digest=sha(raw)
        if expected and expected!=digest:raise ValueError(key+': tracked defining-source hash differs for '+actual)
        return blob(cfg,actual,'`'+actual+'`'),digest,'Tracked defining source'
    if not expected or not re.fullmatch(r'[0-9a-f]{64}',expected):
        raise ValueError(key+': untracked defining source lacks an exact hash: '+actual)
    manifest=git_bytes(worktree,cfg['commit'],proof_path(cfg,'UPSTREAM.json'))
    if manifest is None:raise ValueError(key+': downloaded source lacks tracked UPSTREAM.json')
    matches=[row for row in upstream_items(json.loads(manifest)) if row.get('path')==actual]
    if len(matches)!=1:raise ValueError(key+': upstream definition not uniquely pinned: '+actual)
    item=matches[0]
    if expected not in [item.get('port_sha256'),item.get('ported_sha256'),item.get('sha256')]:
        raise ValueError(key+': manifest and target definition hashes disagree')
    url=item.get('url') or item.get('source_url')
    if not isinstance(url,str) or not url.startswith('https://'):raise ValueError('Upstream source needs HTTPS provenance')
    return f"`{actual}`; {blob(cfg,'UPSTREAM.json','selected-commit source/port manifest')}; [original upstream]({url})",expected,'Downloaded definition; hash denotes checked port, not a tracked blob'


def target_index(base,cfg,meta):
    manifests={k:read_json(base/'harness'/(k+'-targets.json')) for k in cfg}
    counts={k:Counter(t['role'] for t in m['targets']) for k,m in manifests.items()}
    total=sum(sum(c.values()) for c in counts.values())
    state='Final job coordinates read from final-metadata.json.' if meta else 'Preparation index: final job coordinates are not yet selected.'
    parts=['# Exact-version target and original-requirement index',state,
      f'This index maps **{len(cfg)} execution groups and {total} target entries** across ten submissions. Counts are per version, include definitions where explicitly audited, and include repeated declarations across complete-package supplements. This file records inputs and coverage mappings; it does not itself assert that any check passed. Consult the final report and per-target axiom results for the executed verdict.',
      'Each group uses its own selected proof commit. A tracked definition links to that commit. Downloaded definitions link to the selected commit’s immutable source/port manifest and original upstream URL, with the exact checked definition SHA256; no nonexistent proof-commit URL is constructed. Auditor bridges link to their separate harness files. An import entry can differ from the actual defining file without changing what declaration is checked.',
      table(['Group','Problem','Original entries','Auditor bridges','Total','Exact selected proof commit','Execution coordinates'],[
       [k,cfg[k]['id'],counts[k]['theorem'],counts[k]['bridge'],sum(counts[k].values()),f"[`{cfg[k]['commit']}`]({REPO}/commit/{cfg[k]['commit']})",job_link(meta,k)] for k in cfg])]
    for key,c in cfg.items():
        m=manifests[key]
        if m['project']['commit']!=c['commit']:raise ValueError('Manifest/config proof mismatch')
        ids=[t['id'] for t in m['targets']]
        if len(ids)!=len(set(ids)):raise ValueError('Duplicate target ID')
        mapping={i:[] for i in ids};reqs=[]
        for p in m['problems']:
            for r in p['requirements']:
                reqs.append([r['id'],r['description'],', '.join(r['targets']) or 'No mapped target',r.get('coverage','pending')])
                for tid in r['targets']:
                    if tid not in mapping:raise ValueError('Unknown requirement target')
                    mapping[tid].append(r['id'])
        if any(not v for v in mapping.values()):raise ValueError('Unmapped target')
        parts.extend([f'## {key} — {c["id"]}',
          f"Project: `{c['project']}`. Selected branch: `{c['branch']}`. Proof commit: `{c['commit']}`. {job_link(meta,key)}.",
          f"Manifest: [{key}-targets.json](harness/{key}-targets.json), SHA256 `{sha((base/'harness'/(key+'-targets.json')).read_bytes())}`. Auditor bridge SHA256 `{sha((base/'harness'/c['bridge_file']).read_bytes())}`.",
          'Original source(s): '+', '.join(f"[{p['id']}]({p['source']})" for p in m['problems'])+'.',
          'The manifest’s `coverage` label is the preparatory author-entered mapping state; it is neither an executed test outcome nor a substitute for the final separate semantic judgment.',
          table(['Requirement ID','Original requirement / declared supplement','Mapped target IDs','Manifest coverage label'],reqs)])
        rows=[]
        for t in m['targets']:
            link,digest,origin=definition(base,key,c,t)
            if t['role']=='bridge':entry=f"`{t['module']}`; `{t['source']}`; [harness input](harness/{c['bridge_file']})"
            else:
                worktree=base/'sources'/c.get('source_key',key)
                if git_bytes(worktree,c['commit'],proof_path(c,t['source'])) is None:raise ValueError('Original verification entry must be tracked')
                entry=f"`{t['module']}`; {blob(c,t['source'],'`'+t['source']+'`')}"
            rows.append([t['id'],t['role'],', '.join(mapping[t['id']]),'`'+t['declaration']+'`',entry,link,'`'+digest+'`',origin])
        parts.append(table(['Target','Role','Requirement IDs','Fully qualified declaration','Imported verification entry','Actual defining source / provenance','Definition SHA256','Source binding'],rows))
    return '\n\n'.join(parts)+'\n'


def reproduction(base,cfg,meta):
    manifests={k:read_json(base/'harness'/(k+'-targets.json')) for k in cfg}
    status='The final selected jobs below come from final-metadata.json; do not substitute the latest branch tip.' if meta else 'Preparation instructions: final job/harness selection is pending. Regenerate this document after final-metadata.json is fixed. No execution pass is asserted here.'
    rows=[]
    for k,c in cfg.items():
        orig=c['inspection']['original_target_count'];total=len(manifests[k]['targets'])
        rows.append([k,c['project'],f"`{c['commit']}`",f'{orig} + {total-orig} = {total}',job_link(meta,k)])
    parts=['# Reproduce exact-version Lean verification',status,
      'These instructions distinguish three tasks: review already saved raw evidence, rerun the strict archive/evidence inspector, and freshly execute a selected proof in an isolated container. None of these tasks alone decides natural-language correspondence, mathematical completeness, attribution, priority or organizer eligibility.',
      table(['Group','Proof project','Selected proof commit','Original + bridges','Pinned job and harness'],rows),
      '## Review saved evidence and recover original archive identity',
      'The curated delivery contains the complete extracted successful and failed raw evidence, immutable file-hash inventories and external artifact receipts. It intentionally omits duplicate original GitHub artifact ZIP downloads. Do not reconstruct those originals by recompressing the raw files: ZIP metadata, compression and ordering affect their byte identity.',
      'Before running `inspect_evidence.py` or `finalize_report.py --check-only`, obtain each selected group’s **original artifact ZIP** using its `evidence/GROUP/artifact-receipt.json` fields `workflow_run`, `artifact_id` and `filename`. Save it as `evidence/GROUP/FILENAME` beside that receipt. Match both `sha256` and `bytes`. The GitHub artifact URL is `https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/WORKFLOW_RUN/artifacts/ARTIFACT_ID`; its API download endpoint is `https://api.github.com/repos/ketianzhang1-lang/jsp-000301-lean/actions/artifacts/ARTIFACT_ID/zip`. Use your own authorized GitHub session or download client when authentication is required; credentials are never mounted into proof containers.',
      'The workflow requests **90-day artifact retention**, and these receipts were created on 2026-09-20; GitHub may remove an artifact earlier. If its original archive is no longer available, the preserved extracted logs and their hashes remain reviewable, but the original archive-identity gate cannot be rerun from the curated bundle alone. This is an evidence-availability limit, not a reason to weaken the strict inspector.',
      'The complete finalizer also validates retained failed-attempt archives, so recover their original ZIPs from their own receipts as well. Inspecting only successful selected groups requires their successful archives. Failed attempts are historical evidence and never count as successful execution.',
      '''Verify downloaded byte identity from the delivery root without executing proof code:

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

Use repeated `--key` flags, for example `--key 301 --key 897`, when only those groups’ original archives have been recovered. Do not overwrite the canonical execution summary merely to turn a missing-archive result into a pass. The strict finalizer also needs final metadata, selected.json, the published documentation-repair receipts and all ten reviewed scope records.''',
      '## Fresh execution in a disposable verification environment',
      'Prerequisites: Git, Python 3, Bash, Docker and sufficient disk/memory. The recorded GitHub runner uses Ubuntu 24.04, four container CPUs, a 14 GiB memory limit, 24 GiB memory-plus-swap limit, 1,024 processes and an additional 16 GiB host swap allocation. The selected workflow describes that resource setup. Do not run untrusted Lean or Lake commands directly on a credential-bearing host. Preparation downloads pinned dependencies; original build, target audit and replay/checker stages use `--network none`, UID/GID 10001, all capabilities dropped and `no-new-privileges`. Only the disposable proof checkout and evidence directory are writable; harness and checker-tool mounts are read-only during checking.',
      'The recipe below selects `301` as a concrete example. Change only `audit_group` to another row key. Start in the delivery root after final metadata exists; use a fresh working directory for every execution. The selected harness is specific to that group’s actual final job, and can differ from another group’s harness commit. The commands do not claim a new run has the byte identity or timestamp of the historical GitHub job.',
      '''```bash
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
printf '%s  %s\\n' '5db45dddcb4d588bc27e7c7161fbca5cedaa3e73e1c40843d21f5a214323cd07' 'harness/audit.py' | sha256sum --check
git -C official rev-parse HEAD > evidence/OFFICIAL_RULES_COMMIT
printf '%s\\n' "$selected_harness" > evidence/HARNESS_COMMIT
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

A rerun’s dependency downloads, image identity, versions, durations and output hashes must be recorded independently. The Docker base tag is specified in the selected Dockerfile; the historical image ID is evidence for that run and does not imply a future rebuild has byte-identical operating-system packages. Never attach a historical artifact receipt to a newly produced ZIP.''',
      '## What each stage must establish',
      '1. **Prepare:** read exact toolchain and lockfile, bootstrap only hash-pinned upstream sources where configured, prepare Mathlib, and build the pinned exporter and independent checker. The selected proof commit, actual branch containment, every dependency revision and source/configuration bytes are recorded. Full Git history is needed for both supplements’ byte comparison with their base commits.',
      '2. **Original:** remove the project build directory and stale evidence outputs, then execute the selected original verifier without resume. Recompile the full reused dependency closure and local modules, perform original kernel replays, audit every original target, and reject the false arithmetic negative control. Restore only tracked historical evidence after copying the fresh logs; compare source/configuration inputs before and after.',
      '3. **Audit:** place the separately identified auditor bridge under the configured library, strict-compile it with warnings as errors, then invoke the **unchanged** official audit script on the group’s manifest. Its preflight pins the tracked theorem entries; each target gets explicit module build, source check, `#check`, `#print`, and `#print axioms`. Downloaded definition sources and tracked import entries are separately identified in the target index and checked by source hashes.',
      '4. **Replay:** replay the bridge module with the pinned Lean kernel checker; export all listed original and bridge target closures; run NaNoda with hard rejection of any axiom outside `propext`, `Classical.choice`, and `Quot.sound`. Preserve nonempty printed statements, success output, export hash, actual dependency revisions, final source hashes and negative-control evidence. A target can use a subset of those standard foundations.',
      'The official rules and skill are pinned to [awards '+RULES+']('+AWARDS+'/tree/'+RULES+'/skills/lean-verify). The unchanged `audit.py` SHA256 is `'+AUDIT_SHA+'`. The automatic script does not itself determine semantic completeness. Final source-to-statement judgment, original quantifiers, all cases and attribution are separately reviewed.',
      '## Explicit compatibility and module-routing disclosures',
      'All twelve groups use Lean 4.34.0. `lean4export` source commit `6cea97789dc088ea47fcea15692db85685aedac5` originally targets Lean 4.35.0-rc2; the recorded preparation copies the project’s exact 4.34.0 toolchain pin into the exporter checkout and rebuilds that source. This is a disclosed compatibility rebuild, not a claimed native 4.34 exporter release. NaNoda source is `4c544ed4099c8227f07d5de77ad1e69fb0740a27`, built with Rust 1.90.0 and Cargo `--locked`. Neither source pin authorizes changing a proof’s toolchain or dependencies.',
      'JSP-000301’s selected historical proof commit has no strict Python verification script. [301-original.py](harness/301-original.py) is explicitly auditor-owned: it builds and strict-checks the unchanged original module, replays it, audits all eight public declarations, verifies actual dependency revisions and rejects `1=0`. The later historical strict-verification commit is separate evidence and is never substituted for the selected proof version.',
      'Only two native Lake target forms are missing in selected supplement configurations. Their adapters intercept exactly the calls below. Each intercepted call deletes stale output and invokes the **real pinned Lake** to execute `lean -DwarningAsError=true -j1 -M12000 -o OLEAN SOURCE`; all other argument lists pass to the real Lake unchanged. The original proof, lakefile and official audit script remain unchanged. This is manual-equivalent explicit module compilation, not native Lake-target success.',
      table(['Group','Only intercepted command','Actual source','Expected target-audit compilations','Adapter evidence'],[
       ['465-uniform','`lake build +JSP000465Uniform`','`JSP000465Uniform.lean`','5','[adapter](harness/465-uniform-manual-lake-adapter.py); `manual-module-builds.jsonl`, compiler logs and `manual-equivalence.json`'],
       ['897-stability','`lake build +JSP000897Stability`','`JSP000897Stability.lean`','7','[adapter](harness/897-stability-manual-lake-adapter.py); `manual-module-builds.jsonl`, compiler logs and `manual-equivalence.json`']]),
      'The counts above follow the original target declarations requiring each omitted module. Actual successful compilations, stable source hashes, exact commands, unique logs, output hashes and exit codes must be checked in each final raw artifact; adapter existence or an expected count is not execution evidence. Both supplements also rerun their complete base proofs.',
      '## Evidence coordinates and interpretation',
      'For a selected group, `evidence/GROUP/remote/` holds its immutable extracted artifact; `evidence/GROUP/artifact-receipt.json` is the external ZIP receipt. Key records include `targets.json`, `audit/result.json`, `preflight/`, `original-clean-verifier.json`, `fresh-project-evidence/`, any `fresh-extra-1/`, `bridge-precheck.json`, `bridge-kernel.json`, `export-command.json`, `export.ndjson.gz`, `nanoda-config.json`, `nanoda-statements.txt`, `independent-nanoda.log`, `source-before.json`, `source-after.json` and `SHA256SUMS.json`. Exact group-specific locations are defined by config inspection records; a missing expected log is a failure of evidence, not an empty axiom set.',
      'A finished GitHub job or parser exit code alone does not certify a complete original mathematical solution. Preserve failed attempts, distinguish infrastructure and auditor-only corrections from selected proof changes, and report the actual final level of assurance. This self-check does not establish pre-opening historical timing, solver-candidate registration, merge, identity confirmation, priority or an award.']
    return '\n\n'.join(parts)+'\n'


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--base',type=Path,default=ROOT);args=parser.parse_args()
    base=args.base.resolve();cfg=read_json(base/'harness/config.json')
    meta=read_json(base/'final-metadata.json') if (base/'final-metadata.json').is_file() else None
    if meta:
        if meta.get('rules_commit')!=RULES or set(meta.get('jobs',{}))!=set(cfg):raise ValueError('Final metadata group/rules mismatch')
        for k,j in meta['jobs'].items():
            if not re.fullmatch(r'[0-9a-f]{40}',j['harness_commit']):raise ValueError('Invalid harness commit')
            if not isinstance(j['run_id'],int) or not isinstance(j['job_id'],int):raise ValueError('Invalid job coordinates')
    documents={'target-index.md':target_index(base,cfg,meta),'how-to-reproduce.md':reproduction(base,cfg,meta)}
    for name,text in documents.items():
        if any(x in text for x in ('/workspace/','/home/','/Users/','{{VERIFICATION_EVIDENCE}}')):raise ValueError('Private path or unresolved draft token in output')
        path=base/name
        if path.is_symlink():raise ValueError('Refusing symlink destination')
        path.write_text(text,encoding='utf-8')
    print(json.dumps({'groups':len(cfg),'targets':sum(len(read_json(base/'harness'/(k+'-targets.json'))['targets']) for k in cfg),'final_job_coordinates':meta is not None,'documents':list(documents)}))

if __name__=='__main__':main()

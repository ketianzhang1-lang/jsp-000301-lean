#!/usr/bin/env python3
"""Fresh selected-commit checks, executed as an unprivileged Docker user.

The official helper is unmodified. Its result is mechanical evidence, never a
semantic verdict. Preparation has network access; checking has none.
"""
import datetime, hashlib, importlib.util, json, os, pathlib, shutil, subprocess, sys

H = pathlib.Path('/harness')
OUT = pathlib.Path('/audit')
SPEC = next(x for x in json.loads((H/'jobs.json').read_text()) if x['key'] == sys.argv[2])
ROOT = pathlib.Path(SPEC['manifest']['project']['root'])
LAKE = '/tooling/lean/bin/lake'
os.environ['PATH'] = '/tooling/lean/bin:' + os.environ['PATH']
os.environ['LEAN_NUM_THREADS'] = '1'
os.chdir(ROOT)
OUT.mkdir(exist_ok=True)
def dump(path, obj):
    path.write_text(json.dumps(obj, indent=2) + '\n')
def run(argv, label, check=True, timeout=10800):
    log = OUT/(label+'.log')
    print('RUN', label, argv, flush=True)
    with log.open('w') as f:
        r = subprocess.run(argv, stdout=f, stderr=subprocess.STDOUT, timeout=timeout)
    print('EXIT', label, r.returncode, flush=True)
    if r.returncode and check:
        print(log.read_text(errors='replace')[-16000:], flush=True)
        raise RuntimeError(label+' failed')
    return r.returncode
def git(*args):
    return subprocess.check_output(['git','-c','core.hooksPath=/dev/null',*args],text=True).strip()
def pins():
    result = []
    for x in json.loads((ROOT/'lake-manifest.json').read_text())['packages']:
        path=ROOT/'.lake/packages'/x['name']
        actual=git('-C',str(path),'rev-parse','HEAD')
        assert actual==x['rev'], (x['name'], actual, x['rev'])
        assert not git('-C',str(path),'diff','--name-only'), x['name']
        result.append({'name':x['name'],'expected':x['rev'],'actual':actual})
    dump(OUT/'dependency-pins.json',result)

if sys.argv[1]=='prepare':
    version = SPEC['toolchain'].split(':v')[1]
    sha = {'4.34.0':'caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b',
           '4.31.0':'07a633cc8d9151cbc08825ea4cdda50d4b02a2c9cb852c0131b13046f49cad7f'}[version]
    archive=pathlib.Path('/tooling/lean.tar.zst')
    url=f'https://github.com/leanprover/lean4/releases/download/v{version}/lean-{version}-linux.tar.zst'
    run(['curl','-fL','--retry','3',url,'-o',str(archive)],'download-toolchain')
    actual=hashlib.file_digest(archive.open('rb'),'sha256').hexdigest()
    assert actual==sha, 'Official Lean release checksum mismatch'
    pathlib.Path('/tooling/lean').mkdir()
    run(['tar','--zstd','-xf',str(archive),'--strip-components=1','-C','/tooling/lean'],'unpack-toolchain')
    archive.unlink()
    dump(OUT/'toolchain-origin.json',{'url':url,'sha256':actual,'toolchain':SPEC['toolchain']})
    if (ROOT/'scripts/bootstrap.py').exists():
        run(['python3','scripts/bootstrap.py'],'bootstrap')
    run([LAKE,'exe','cache','get','Mathlib'],'mathlib-cache')
    pins()
    sys.exit(0)

assert sys.argv[1]=='check'
assert git('rev-parse','HEAD')==SPEC['ref']
assert not git('diff','--name-only'), 'Tracked checkout dirty before checking'
assert (ROOT/'lean-toolchain').read_text().strip()==SPEC['toolchain']
pins()
dump(OUT/'execution.json',{'started_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'proof_commit':SPEC['ref'],'execution':'GitHub Actions ephemeral runner, non-root Docker, checking network disabled',
    'preparation_network':'Enabled only for pinned toolchain, pinned dependencies and checksum-verified upstream sources',
    'mathlib_cache':'Official pinned Mathlib cache; local project build products removed before the source rebuild',
    'container_limits':'2 CPUs, 6 GiB RAM, 14 GiB RAM+swap, 2048 PIDs; cap-drop ALL; no-new-privileges; read-only root filesystem'})
manifest=SPEC['manifest']; dump(OUT/'targets.json',manifest)
run(['python3',str(H/'official-skill/scripts/audit.py'),'preflight',str(OUT/'targets.json'),'--out',str(OUT/'preflight')],'preflight')
build_dir=ROOT/'.lake/build'
if build_dir.exists(): shutil.rmtree(build_dir)
run(SPEC['build'],'clean-build-kernel-axioms-negative-control')
# Preserve newly produced verifier logs separately, then restore ONLY tracked
# receipt/log files. Source/config changes are never restored or concealed.
for name in ('evidence','evidence-complete','evidence-selection'):
    d=ROOT/name
    if d.exists(): shutil.copytree(d,OUT/('fresh-'+name))
changed=git('diff','--name-only').splitlines()
dump(OUT/'tracked-changes-after-rebuild.json',changed)
for path in changed:
    rel=pathlib.Path(path).relative_to(pathlib.Path(SPEC['dir'])) if SPEC['dir'] else pathlib.Path(path)
    assert rel.parts[0] in {'evidence','evidence-complete','evidence-selection'}, 'Verification changed non-evidence input: '+path
    subprocess.run(['git','-C','/work','restore','--source',SPEC['ref'],'--',path],check=True)
pins()
code=run(['python3',str(H/'official-skill/scripts/audit.py'),'run',str(OUT/'targets.json'),
    '--out',str(OUT/'official-run'),'--lake',LAKE,'--timeout','1800'],'official-helper',check=False)
result=json.loads((OUT/'official-run/result.json').read_text())
fallback=[]
if code:
    assert result.get('inputs_stable'), 'Helper input instability or precondition failure'
    spec=importlib.util.spec_from_file_location('official_audit',H/'official-skill/scripts/audit.py')
    helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
    for target,row in zip(manifest['targets'],result['targets']):
        if row['status']=='standard_axioms_only': continue
        # Only Lake discovery limitations qualify for a manual equivalent.
        rec=row['commands'][0]
        log=pathlib.Path(rec['log']).read_text(errors='replace')
        assert rec['exit_code']!=0 and any(s in log.lower() for s in ('unknown module','unknown target','no such target','not found in package')), (row,log[-4000:])
        td=OUT/('manual-'+target['id']);td.mkdir()
        src=td/'Audit.lean';src.write_text(helper.audit_source(target))
        commands=[[LAKE,'env','lean','-DwarningAsError=true',str(ROOT/target['source'])],
                  [LAKE,'env','lean',str(src)]]
        records=[helper.capture(cmd,ROOT,td/f'{i}.log',1800) for i,cmd in enumerate(commands)]
        assert all(r['status']=='ok' for r in records), records
        axioms=helper.parse_axioms((td/'1.log').read_text(),target['declaration'])
        assert helper.classify(axioms)=='standard_axioms_only', axioms
        fallback.append({'id':target['id'],'declaration':target['declaration'],'reason':log,'commands':records,'axioms':axioms,
                         'explicit_build':'The unchanged clean source verification script compiled this source to its correct module .olean; the two commands recheck source and audit the loaded declaration.'})
dump(OUT/'manual-equivalents.json',fallback)
dump(OUT/'mechanical-result.json',{'all_selected_targets_checked':True,
    'official_helper_exit_code':code,'manual_equivalent_count':len(fallback),
    'target_count':len(manifest['targets']),'semantic_verdict':'Requires separate source/statement/coverage review; no automatic mathematical verdict',
    'finished_at':datetime.datetime.now(datetime.timezone.utc).isoformat()})
print('ALL SELECTED TARGET CHECKS FINISHED; SEMANTIC REVIEW STILL REQUIRED',flush=True)

import sys, pathlib, subprocess, json, time, hashlib, shutil, re, os

stage, key = sys.argv[1:]
config=json.loads(pathlib.Path('/harness/config.json').read_text())[key]
project=pathlib.Path('/work')/config['project'];out=pathlib.Path('/out');out.mkdir(exist_ok=True)
def run(name,args,cwd=project,limit=1200):
    start=time.time();print('START',name,flush=True)
    with (out/(name+'.log')).open('wb') as f:
        try:r=subprocess.run(args,cwd=cwd,stdout=f,stderr=subprocess.STDOUT,timeout=limit);code=r.returncode
        except subprocess.TimeoutExpired:code=124
    (out/(name+'.json')).write_text(json.dumps({'argv':args,'cwd':str(cwd),'exit_code':code,'seconds':time.time()-start}))
    print('END',name,code,flush=True)
    if code:raise SystemExit(code)
def pin(url,sha,path):
    run('init-'+path.name,['git','init',str(path)],out)
    run('fetch-'+path.name,['git','-C',str(path),'fetch','--depth','1',url,sha],out)
    run('checkout-'+path.name,['git','-C',str(path),'checkout','--detach',sha],out)
if stage=='prepare':
    run('versions',['bash','-c','lean --version; lake --version; rustc --version; cargo --version; id; uname -a'])
    run('cache',['lake','exe','cache','get'])
    tools=out/'tools';tools.mkdir(exist_ok=True)
    pin('https://github.com/leanprover/lean4export.git','6cea97789dc088ea47fcea15692db85685aedac5',tools/'exporter')
    pin('https://github.com/ammkrn/nanoda_lib.git','4c544ed4099c8227f07d5de77ad1e69fb0740a27',tools/'checker')
    shutil.copyfile(project/'lean-toolchain',tools/'exporter/lean-toolchain')
    run('build-exporter',['lake','build'],tools/'exporter')
    run('build-checker',['cargo','build','--release','--locked'],tools/'checker')
elif stage=='verify':
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()==config['commit']
    # Remove local generated outputs, retaining only cache of trusted pinned dependencies.
    shutil.rmtree(project/'.lake/build',ignore_errors=True)
    tracked=subprocess.check_output(['git','ls-files'],cwd=project,text=True).splitlines()
    assert not any(p.endswith(('.olean','.ilean','.so')) for p in tracked)
    before={p:hashlib.sha256((project/p).read_bytes()).hexdigest() for p in tracked if (project/p).is_file()}
    (out/'source-before.json').write_text(json.dumps(before,indent=2))
    # Avoid treating committed historical evidence files overwritten by the old verifier as source changes.
    run('clean-build',['lake','build','--wfail'])
    run('historical-verifier',['bash','scripts/verify.sh'])
    shutil.copytree(project/'evidence',out/'fresh-project-evidence',dirs_exist_ok=True)
    if any(p.startswith('evidence/') for p in tracked):
        run('restore-historical-evidence',['git','restore','--','evidence'])
    bridge=project/config['bridge_path'];bridge.parent.mkdir(exist_ok=True)
    shutil.copyfile('/harness/'+config['bridge_file'],bridge)
    manifest=json.loads(pathlib.Path('/harness/'+key+'-targets.json').read_text())
    manifest['project']['root']=str(project)
    target=out/'targets.json';target.write_text(json.dumps(manifest,indent=2))
    run('official-preflight',['python3','/harness/audit.py','preflight',str(target),'--out','/out/preflight'])
    run('official-audit',['python3','/harness/audit.py','run',str(target),'--out','/out/audit','--lake','/opt/elan/toolchains/leanprover--lean4---v4.34.0/bin/lake','--timeout','300'],limit=2400)
    run('bridge-kernel',['lake','env','leanchecker',config['bridge_module']])
    names=[t['declaration'] for t in manifest['targets']]
    export=out/'export.ndjson'
    args=['lake','env','/out/tools/exporter/.lake/build/bin/lean4export',config['bridge_module'],'--']+names
    with export.open('wb') as f:
        r=subprocess.run(args,cwd=project,stdout=f,stderr=subprocess.PIPE,timeout=600)
    (out/'export-stderr.log').write_bytes(r.stderr)
    (out/'export-command.json').write_text(json.dumps({'argv':args,'exit_code':r.returncode}))
    if r.returncode:raise SystemExit(r.returncode)
    nc={'export_file_path':str(export),'use_stdin':False,'permitted_axioms':['propext','Classical.choice','Quot.sound'],'unpermitted_axiom_hard_error':True,'nat_extension':True,'string_extension':True,'pp_declars':names,'pp_output_path':'/out/nanoda-statements.txt','pp_to_stdout':False,'print_success_message':True}
    (out/'nanoda-config.json').write_text(json.dumps(nc));(out/'nanoda-statements.txt').write_text('')
    run('independent-nanoda',['/out/tools/checker/target/release/nanoda_bin','/out/nanoda-config.json'])
    run('dependencies',['python3','-c',"import json,subprocess;from pathlib import Path;ps=json.loads(Path('lake-manifest.json').read_text())['packages'];actual={p['name']:subprocess.check_output(['git','-C','.lake/packages/'+p['name'],'rev-parse','HEAD'],text=True).strip() for p in ps};print(json.dumps(actual,indent=2));assert all(actual[p['name']]==p['rev'] for p in ps)"])
    after={p:hashlib.sha256((project/p).read_bytes()).hexdigest() for p in before}
    # Historical evidence restored above; all pinned tracked inputs must remain identical.
    assert before==after
    (out/'source-after.json').write_text(json.dumps(after,indent=2))
    run('final-status',['git','status','--porcelain','--untracked-files=all'])
    run('compress-export',['gzip','-n',str(export)],out)
    (out/'mechanical-completion.json').write_text(json.dumps({'proof_commit':config['commit'],'mechanical_checks':'completed','semantic_verdict':'requires separate review','network_during_verification':'disabled','targets':len(names)}))

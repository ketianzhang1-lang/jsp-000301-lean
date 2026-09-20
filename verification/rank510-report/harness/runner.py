import sys,pathlib,subprocess,json,time,hashlib,shutil,os,threading
stage,key=sys.argv[1:];cfg=json.loads(pathlib.Path('/harness/config.json').read_text())[key]
project=pathlib.Path('/work')/cfg['project'];out=pathlib.Path('/out');out.mkdir(exist_ok=True)
os.environ.update(cfg.get('environment',{}))
def run(name,args,cwd=project,limit=1800):
 start=time.time();print('START',name,flush=True)
 with (out/(name+'.log')).open('wb') as f:
  try:r=subprocess.run(args,cwd=cwd,stdout=f,stderr=subprocess.STDOUT,timeout=limit);code=r.returncode
  except subprocess.TimeoutExpired:code=124
 (out/(name+'.json')).write_text(json.dumps({'argv':args,'cwd':str(cwd),'exit_code':code,'seconds':time.time()-start}))
 print('END',name,code,flush=True)
 if code:
  print((out/(name+'.log')).read_text(errors='replace')[-16000:],flush=True);raise SystemExit(code)
def tracked():return subprocess.check_output(['git','ls-files'],cwd=project,text=True).splitlines()
def hashes(names):return {p:hashlib.sha256((project/p).read_bytes()).hexdigest() for p in names if (project/p).is_file()}
def pin(url,sha,path):
 run('init-'+path.name,['git','init',str(path)],out);run('fetch-'+path.name,['git','-C',str(path),'fetch','--depth','1',url,sha],out);run('checkout-'+path.name,['git','-C',str(path),'checkout','--detach',sha],out)
if stage=='prepare':
 before=hashes(tracked());(out/'tracked-before-prepare.json').write_text(json.dumps(before,indent=2))
 run('versions',['bash','-c','set -e; lean --version; lake --version; rustc --version; cargo --version; id; uname -a'])
 if cfg.get('bootstrap'):run('bootstrap',cfg['bootstrap'],limit=3600)
 for i,args in enumerate(cfg['prepare_commands']):run('prepare-dependencies-'+str(i),args,limit=3600)
 after=hashes(before);(out/'tracked-after-prepare.json').write_text(json.dumps(after,indent=2));assert before==after, 'Tracked inputs changed during preparation'
 tools=out/'tools';tools.mkdir(exist_ok=True)
 pin('https://github.com/leanprover/lean4export.git',cfg['exporter_commit'],tools/'exporter')
 pin('https://github.com/ammkrn/nanoda_lib.git',cfg['nanoda_commit'],tools/'checker')
 shutil.copyfile(project/'lean-toolchain',tools/'exporter/lean-toolchain')
 run('build-exporter',['lake','build'],tools/'exporter');run('build-checker',['cargo','build','--release','--locked'],tools/'checker')
elif stage=='original':
 frozen=json.loads((out/'tracked-after-prepare.json').read_text());assert hashes(frozen)==frozen,'Tracked input changed between stages'
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()==cfg['commit']
 shutil.rmtree(project/'.lake/build',ignore_errors=True)
 names=tracked();assert not any(p.endswith(('.olean','.ilean','.so')) for p in names)
 extras=[str(p.relative_to(project)) for p in project.rglob('*.lean') if not any(x in p.relative_to(project).parts for x in ['.lake','.git']) and not str(p.relative_to(project)).startswith('evidence')]
 before=hashes(sorted(set(names+extras)));(out/'source-before.json').write_text(json.dumps(before,indent=2))
 run('original-clean-verifier',cfg['verify_command'],limit=10800)
 for i,d in enumerate([cfg['evidence_dir']]+cfg.get('additional_evidence_dirs',[])):
  shutil.copytree(project/d,out/('fresh-project-evidence' if i==0 else 'fresh-extra-'+str(i)),dirs_exist_ok=True)
 restore=[p for p in names if p.split('/')[0].startswith('evidence')]
 if restore:run('restore-historical-evidence',['git','restore','--']+restore)
 assert hashes(before)==before,'Pinned input changed during original verification'
 for prefix in cfg.get('extra_kernel_prefixes',[]):run('extra-kernel-'+prefix,['lake','env','leanchecker','--verbose',prefix],limit=3600)
 (out/'original-completion.json').write_text(json.dumps({'commit':cfg['commit'],'original_clean_verification':'completed','inputs_stable':True}))
elif stage=='audit':
 bridge=project/cfg['bridge_path'];bridge.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile('/harness/'+cfg['bridge_file'],bridge)
 bridge_output=project/'.lake/build/lib/lean'/pathlib.Path(cfg['bridge_module'].replace('.','/')+'.olean');bridge_output.parent.mkdir(parents=True,exist_ok=True)
 run('bridge-precheck',['lake','env','lean','-DwarningAsError=true','-j1','-M12000','-o',str(bridge_output),str(bridge)],limit=2400)
 manifest=json.loads(pathlib.Path('/harness/'+key+'-targets.json').read_text());manifest['project']['root']=str(project)
 target=out/'targets.json';target.write_text(json.dumps(manifest,indent=2))
 run('official-preflight',['python3','/harness/audit.py','preflight',str(target),'--out','/out/preflight'])
 audit_lake=shutil.which('lake')
 if cfg.get('lake_adapter'):
  assert key=='506-selection', 'Manual Lake adapter is scoped to 506-selection'
  assert audit_lake and pathlib.Path(audit_lake).is_absolute(), 'Trusted absolute Lake path required'
  adapter_src=pathlib.Path('/harness')/cfg['lake_adapter']['file'];adapter=out/'manual-lake-adapter'
  shutil.copyfile(adapter_src,adapter);adapter.chmod(0o755)
  os.environ['LEAN_VERIFY_REAL_LAKE']=audit_lake
  (out/'manual-equivalence.json').write_text(json.dumps({'real_lake':audit_lake,'adapter':str(adapter),'adapter_sha256':hashlib.sha256(adapter.read_bytes()).hexdigest(),'scope':cfg['lake_adapter'],'official_audit_script_unchanged':True,'proof_lakefile_unchanged':True},indent=2))
  audit_lake=str(adapter)
 run('official-audit',['python3','/harness/audit.py','run',str(target),'--out','/out/audit','--lake',audit_lake,'--timeout','2400'],limit=14400)
elif stage=='replay':
 manifest=json.loads((out/'targets.json').read_text());names=[t['declaration'] for t in manifest['targets']]
 run('bridge-kernel',['lake','env','leanchecker',cfg['bridge_module']],limit=3600)
 export=out/'export.ndjson';args=['lake','env','/out/tools/exporter/.lake/build/bin/lean4export',cfg['bridge_module'],'--']+names
 start=time.time()
 with export.open('wb') as f:r=subprocess.run(args,cwd=project,stdout=f,stderr=subprocess.PIPE,timeout=1800)
 (out/'export-stderr.log').write_bytes(r.stderr);(out/'export-command.json').write_text(json.dumps({'argv':args,'cwd':str(project),'exit_code':r.returncode,'seconds':time.time()-start}))
 if r.returncode:raise SystemExit(r.returncode)
 nc={'export_file_path':str(export),'use_stdin':False,'permitted_axioms':['propext','Classical.choice','Quot.sound'],'unpermitted_axiom_hard_error':True,'nat_extension':True,'string_extension':True,'pp_declars':names,'pp_output_path':'/out/nanoda-statements.txt','pp_to_stdout':False,'print_success_message':True}
 (out/'nanoda-config.json').write_text(json.dumps(nc));(out/'nanoda-statements.txt').write_text('')
 run('independent-nanoda',['/out/tools/checker/target/release/nanoda_bin','/out/nanoda-config.json'],limit=3600)
 run('dependencies',['python3','-c',"import json,subprocess;from pathlib import Path;ps=json.loads(Path('lake-manifest.json').read_text())['packages'];a={p['name']:subprocess.check_output(['git','-C','.lake/packages/'+p['name'],'rev-parse','HEAD'],text=True).strip() for p in ps};print(json.dumps(a,indent=2));assert all(a[p['name']]==p['rev'] for p in ps)"])
 before=json.loads((out/'source-before.json').read_text());after=hashes(before);assert before==after
 (out/'source-after.json').write_text(json.dumps(after,indent=2));snap=out/'checked-source';snap.mkdir(exist_ok=True)
 for n in before:
  if n.endswith(('.lean','.json','.md','.toml','.py','.sh')) and not n.startswith('evidence'):
   d=snap/n;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(project/n,d)
 run('final-status',['git','status','--porcelain','--untracked-files=all'])
 run('compress-export',['gzip','-n',str(export)],out)
 (out/'mechanical-completion.json').write_text(json.dumps({'proof_commit':cfg['commit'],'mechanical_checks':'completed','semantic_verdict':'requires separate review','network_during_verification':'disabled','targets':len(names)}))
else:raise SystemExit('Unknown stage')

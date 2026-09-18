#!/usr/bin/env python3
"""Verify the complete pinned tiling proof and the integration theorem."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
os.chdir(ROOT);os.environ['LEAN_NUM_THREADS']='1'
EVIDENCE=ROOT/'evidence-complete';EVIDENCE.mkdir(exist_ok=True)
def run(args,name):
    p=EVIDENCE/name
    with p.open('w') as log:
        r=subprocess.run(args,stdout=log,stderr=subprocess.STDOUT)
    if r.returncode:
        print(p.read_text()[-16000:],flush=True)
        raise SystemExit('Failed: '+' '.join(args))
    print('Passed: '+' '.join(args),flush=True)
run([sys.executable,'scripts/bootstrap.py'],'bootstrap.log')
manifest=json.loads(Path('lake-manifest.json').read_text())
for pkg in manifest['packages']:
    actual=subprocess.check_output(['git','-C','.lake/packages/'+pkg['name'],'rev-parse','HEAD'],text=True).strip()
    if actual!=pkg['rev']:raise SystemExit('Wrong dependency revision: '+pkg['name'])
sources={x['path'][:-5].replace('/','.'):Path(x['path']) for x in json.loads(Path('UPSTREAM.json').read_text())}
for n in ['JSP000388','JSP000388Complete','AuditComplete']:sources[n]=Path(n+'.lean')
order=[]
def visit(n):
    if n in order:return
    for d in re.findall(r'^import\s+(\S+)',sources[n].read_text(),re.M):
        if d in sources:visit(d)
    order.append(n)
visit('AuditComplete')
progress=EVIDENCE/'build-progress.json'
# --resume is only for an interrupted local invocation. Each reused module must
# have its exact source hash, an existing object, and a successful saved build log.
resume=json.loads(progress.read_text()) if '--resume' in sys.argv and progress.exists() else {}
done={}
for n in order:
    src=sources[n];digest=hashlib.sha256(src.read_bytes()).hexdigest()
    out=Path('.lake/build/lib/lean')/(n.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
    log=EVIDENCE/('build-'+n+'.log')
    if resume.get(n)!=digest or not out.exists() or not log.exists() or re.search(r'\berror:',log.read_text()):
        run(['lake','env','lean','-DwarningAsError=true','-j1','-M10000','-o',str(out),'./'+str(src)],'build-'+n+'.log')
    done[n]=digest;progress.write_text(json.dumps(done,indent=2)+'\n')
    print('Compiled/verified source:',n,flush=True)
# Re-run the audit against the completed objects even on resumed builds.
run(['lake','env','lean','-DwarningAsError=true','AuditComplete.lean'],'axioms.log')
expected=re.findall(r'^#print axioms (\S+)',Path('AuditComplete.lean').read_text(),re.M)
log=(EVIDENCE/'axioms.log').read_text();allowed={'propext','Classical.choice','Quot.sound'}
if len(expected)!=18:raise SystemExit('Unexpected audit target count')
for name in expected:
    m=re.search("'"+re.escape(name)+r"' depends on axioms:\s*\[([^]]*)\]",log)
    if m:
        if not {x.strip() for x in m[1].split(',') if x.strip()}<=allowed:raise SystemExit('Unexpected axiom: '+name)
    elif "'"+name+"' does not depend on any axioms" not in log:raise SystemExit('Missing axiom report: '+name)
for n in ['ErdosProblems.Erdos477','JSP000388','JSP000388Complete']:
    run(['lake','env','leanchecker','--verbose',n],'kernel-'+n+'.log')
negative=Path('NegativeComplete.lean');negative.write_text('import JSP000388Complete\nexample : (1 : Nat) = 0 := by decide\n')
r=subprocess.run(['lake','env','lean',str(negative)],capture_output=True,text=True)
negative.unlink();(EVIDENCE/'negative-control.log').write_text(r.stdout+r.stderr)
if r.returncode==0 or 'is false' not in r.stdout+r.stderr:raise SystemExit('Unexpected negative-control result')
for n in order:
    if hashlib.sha256(sources[n].read_bytes()).hexdigest()!=done[n]:raise SystemExit('Source changed during verification: '+n)
record={'status':'passed','toolchain':Path('lean-toolchain').read_text().strip(),
'preparation_head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
'modules_compiled':order,'axiom_reports':len(expected),'allowed_axioms':sorted(allowed),
'dependency_count':len(manifest['packages']),'kernel_prefixes':['ErdosProblems.Erdos477','JSP000388','JSP000388Complete'],
'source_sha256':{str(sources[n]):done[n] for n in order},
'object_sha256':{n:hashlib.sha256((Path('.lake/build/lib/lean')/(n.replace('.','/')+'.olean')).read_bytes()).hexdigest() for n in order},
'limits':'Contributor-run compilation and replay with cached pinned Mathlib. Resumed local builds are explicitly hash-matched. No independent human certification.'}
(EVIDENCE/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
print('All full-development checks passed.',flush=True)

#!/usr/bin/env python3
"""Compile and audit the complete pinned JSP-000554 development."""
import hashlib,json,os,re,subprocess,sys,concurrent.futures
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
os.chdir(ROOT);os.environ['LEAN_NUM_THREADS']='1'
EVIDENCE=ROOT/'evidence-complete';EVIDENCE.mkdir(exist_ok=True)
def run(args,name):
    p=EVIDENCE/name
    with p.open('w') as log:
        r=subprocess.run(args,stdout=log,stderr=subprocess.STDOUT)
    if r.returncode:
        print(p.read_text()[-20000:],flush=True)
        raise SystemExit('Failed: '+' '.join(args))
    print('Passed: '+' '.join(args),flush=True)
run([sys.executable,'scripts/bootstrap.py'],'bootstrap.log')
run(['sha256sum','--check','ORIGINAL_PROOF_SHA256'],'original-proof.log')
manifest=json.loads(Path('lake-manifest.json').read_text())
for pkg in manifest['packages']:
    actual=subprocess.check_output(['git','-C','.lake/packages/'+pkg['name'],'rev-parse','HEAD'],text=True).strip()
    if actual!=pkg['rev']:raise SystemExit('Wrong dependency revision: '+pkg['name'])
sources={x['path'][:-5].replace('/','.'):Path(x['path']) for x in json.loads(Path('UPSTREAM.json').read_text())}
for n in ['JSP000554','JSP000554Complete','AuditComplete']:sources[n]=Path(n+'.lean')
order=[];visiting=set();deps={}
def visit(n):
    if n in order:return
    if n in visiting:raise SystemExit('Import cycle: '+n)
    visiting.add(n);deps[n]=[]
    for d in re.findall(r'^(?:public )?import\s+(\S+)',sources[n].read_text(),re.M):
        if d in sources:
            visit(d);deps[n].append(d)
        elif d.startswith(('ErdosProblems.','UnitFractions.','PrimeNumberTheoremAnd.','Util.')):
            raise SystemExit('Unpinned upstream import: '+d)
    visiting.remove(n);order.append(n)
visit('AuditComplete')
if set(order)!=set(sources) or len(order)!=54:raise SystemExit('Unexpected unused source manifest entry')
progress=EVIDENCE/'build-progress.json'
resume=json.loads(progress.read_text()) if '--resume' in sys.argv and progress.exists() else {}
done={};fingerprints={};source_hashes={}
for n in order:
    digest=hashlib.sha256(sources[n].read_bytes()).hexdigest()
    source_hashes[n]=digest
    fingerprints[n]=hashlib.sha256((digest+''.join(fingerprints[d] for d in deps[n])).encode()).hexdigest()
# Compile independent modules concurrently, after their imported modules complete.
workers=int(os.environ.get('JSP554_BUILD_JOBS','2'))
if workers not in (1,2,3):raise SystemExit('JSP554_BUILD_JOBS must be 1, 2 or 3')
pending=set(order);running={};failed=None
with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
    while pending or running:
        for n in order:
            if n not in pending or not all(d in done for d in deps[n]):continue
            if len(running)>=workers or failed:break
            pending.remove(n)
            out=Path('.lake/build/lib/lean')/(n.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
            log=EVIDENCE/('build-'+n+'.log')
            if resume.get(n)==fingerprints[n] and out.exists() and log.exists() and not re.search(r'\berror:',log.read_text()):
                done[n]=fingerprints[n]
                print('Reused hash-matched source:',n,flush=True)
                continue
            future=pool.submit(run,['lake','env','lean','-DwarningAsError=true','-j1','-M8000','-o',str(out),'./'+str(sources[n])],'build-'+n+'.log')
            running[future]=n
        if not running:
            if failed:break
            if pending:continue
            break
        ready,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
        for future in ready:
            n=running.pop(future)
            try:future.result()
            except BaseException as error:
                failed=error
            else:
                done[n]=fingerprints[n]
                progress.write_text(json.dumps(done,indent=2)+'\n')
                print('Compiled source:',n,flush=True)
        if failed and not running:break
if failed:raise SystemExit(str(failed))
run(['lake','env','lean','-DwarningAsError=true','AuditComplete.lean'],'axioms.log')
expected=re.findall(r'^#print axioms (\S+)',Path('AuditComplete.lean').read_text(),re.M)
log=(EVIDENCE/'axioms.log').read_text();allowed={'propext','Classical.choice','Quot.sound'}
if len(expected)!=37 or len(set(expected))!=37:raise SystemExit('Unexpected audit targets')
for name in expected:
    m=re.search("'"+re.escape(name)+r"' depends on axioms:\s*\[([^]]*)\]",log)
    if m:
        if not {x.strip() for x in m[1].split(',') if x.strip()}<=allowed:raise SystemExit('Unexpected axiom: '+name)
    elif "'"+name+"' does not depend on any axioms" not in log:raise SystemExit('Missing axiom report: '+name)
prefixes=['PrimeNumberTheoremAnd','UnitFractions','ErdosProblems','Util','JSP000554','JSP000554Complete']
for n in prefixes:
    run(['lake','env','leanchecker','--verbose',n],'kernel-'+n+'.log')
negative=Path('NegativeComplete.lean');negative.write_text('import JSP000554Complete\nexample : (1 : Nat) = 0 := by decide\n')
r=subprocess.run(['lake','env','lean',str(negative)],capture_output=True,text=True)
negative.unlink();(EVIDENCE/'negative-control.log').write_text(r.stdout+r.stderr)
if r.returncode==0 or 'is false' not in r.stdout+r.stderr:raise SystemExit('Unexpected negative-control result')
for n in order:
    if hashlib.sha256(sources[n].read_bytes()).hexdigest()!=source_hashes[n]:raise SystemExit('Source changed during verification: '+n)
record={'status':'passed','toolchain':Path('lean-toolchain').read_text().strip(),
'preparation_head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
'modules_compiled':order,'axiom_reports':len(expected),'allowed_axioms':sorted(allowed),
'dependency_count':len(manifest['packages']),'kernel_prefixes':prefixes,
'source_sha256':{str(sources[n]):source_hashes[n] for n in order},
'limits':'Contributor-run compilation and replay with cached pinned Mathlib. Local --resume fingerprints include transitive source dependencies. No independent human review.'}
(EVIDENCE/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
run([sys.executable,'scripts/crosscheck.py'],'finite-crosscheck.json')
print('All complete-development checks passed.',flush=True)

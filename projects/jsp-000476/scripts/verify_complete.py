#!/usr/bin/env python3
"""Compile the pinned import closure, audit transitive axioms, and replay the kernel."""
from pathlib import Path
import concurrent.futures, hashlib, json, os, re, subprocess, sys

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT); os.environ['LEAN_NUM_THREADS'] = '1'
EVIDENCE = ROOT / 'evidence-complete'; EVIDENCE.mkdir(exist_ok=True)
LEAN_OPTIONS = ['-DwarningAsError=true', '-DmaxSynthPendingDepth=3', '-DrelaxedAutoImplicit=false']

def run(args, logname):
    path = EVIDENCE / logname
    with path.open('w') as log: result = subprocess.run(args, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        print(path.read_text()[-14000:], flush=True)
        raise RuntimeError('Failed: ' + ' '.join(args))

def uncomment(text):
    # Lean has nested block comments. Preserve newlines so imports remain anchored.
    output=[]; i=0; depth=0
    while i < len(text):
        if text[i:i+2]=='/-': depth+=1; i+=2
        elif depth and text[i:i+2]=='-/': depth-=1; i+=2
        elif not depth and text[i:i+2]=='--':
            end=text.find('\n',i); i=len(text) if end<0 else end
        else:
            if not depth or text[i]=='\n': output.append(text[i])
            i+=1
    return ''.join(output)

run([sys.executable, 'scripts/bootstrap.py'], 'bootstrap.log')
version = subprocess.check_output(['lake', 'env', 'lean', '--version'], text=True)
assert 'version 4.33.0,' in version, version
(EVIDENCE / 'lean-version.txt').write_text(version)
manifest = json.loads(Path('lake-manifest.json').read_text())
for p in manifest['packages']:
    actual=subprocess.check_output(['git','-C','.lake/packages/'+p['name'],'rev-parse','HEAD'],text=True).strip()
    assert actual==p['rev'], 'Wrong dependency: '+p['name']
entries=json.loads(Path('UPSTREAM.json').read_text())
sources={e['path'][:-5].replace('/','.'):Path(e['path']) for e in entries}
for name in ['JSP000476','JSP000476Complete','AuditComplete']: sources[name]=Path(name+'.lean')
deps={}; order=[]; visiting=set()
def visit(name):
    if name in order:return
    assert name not in visiting, 'Import cycle: '+name
    visiting.add(name); deps[name]=[]
    for line in re.findall(r'^(?:public )?import\s+([^\n]+)', uncomment(sources[name].read_text()), re.M):
        for d in line.split():
            if d in sources: visit(d); deps[name].append(d)
            elif not d.startswith(('Mathlib','Lean','Std','Batteries','Qq','Aesop','Plausible')):
                raise RuntimeError('Unpinned import: '+d)
    visiting.remove(name); order.append(name)
visit('AuditComplete')
assert set(order)==set(sources), 'Unexpected unused upstream source'
source_hashes={n:hashlib.sha256(sources[n].read_bytes()).hexdigest() for n in order}
fingerprints={}
environment=hashlib.sha256((Path('lake-manifest.json').read_text()+version+repr(LEAN_OPTIONS)).encode()).hexdigest()
for n in order:
    fingerprints[n]=hashlib.sha256((environment+source_hashes[n]+''.join(fingerprints[d] for d in deps[n])).encode()).hexdigest()
progress=EVIDENCE/'build-progress.json'
resume=json.loads(progress.read_text()) if '--resume' in sys.argv and progress.exists() else {}
done={}; pending=set(order); running={}; failed=None
workers=int(os.environ.get('JSP476_BUILD_JOBS','3')); assert 1<=workers<=4
with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
    while pending or running:
        for n in order:
            if n not in pending or not all(d in done for d in deps[n]):continue
            if len(running)>=workers or failed:break
            pending.remove(n)
            out=Path('.lake/build/lib/lean')/(n.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
            log='build-'+n+'.log'
            if resume.get(n)==fingerprints[n] and out.exists() and (EVIDENCE/log).exists():
                done[n]=fingerprints[n];continue
            future=pool.submit(run,['lake','env','lean',*LEAN_OPTIONS,'-j1','-M12000','-o',str(out),'./'+str(sources[n])],log)
            running[future]=n
        if not running:
            if failed:break
            if pending:continue
            break
        ready,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
        for future in ready:
            n=running.pop(future)
            try: future.result()
            except BaseException as error: failed=error
            else:
                done[n]=fingerprints[n];progress.write_text(json.dumps(done,indent=2)+'\n')
                print(f'Compiled {len(done)}/{len(order)}: {n}',flush=True)
        if failed and not running:break
if failed:raise SystemExit(str(failed))
run(['lake','env','lean',*LEAN_OPTIONS,'AuditComplete.lean'],'axioms.log')
expected=json.loads(Path('AUDIT_TARGETS.json').read_text())
assert re.findall(r'^#print axioms (\S+)',Path('AuditComplete.lean').read_text(),re.M)==expected
log=(EVIDENCE/'axioms.log').read_text();allowed={'propext','Classical.choice','Quot.sound'}
for name in expected:
    match=re.search("'"+re.escape(name)+r"' depends on axioms:\s*\[([^]]*)\]",log)
    if match:assert {a.strip() for a in match[1].split(',') if a.strip()}<=allowed,name
    else:assert "'"+name+"' does not depend on any axioms" in log,name
for n in ['JSP000476','JSP000476Complete']:
    run(['lake','env','leanchecker','--fresh','--verbose',n],'kernel-'+n+'.log')
negative=Path('NegativeComplete.lean');negative.write_text('import JSP000476Complete\nexample : (1 : Nat) = 0 := by decide\n')
r=subprocess.run(['lake','env','lean',str(negative)],capture_output=True,text=True);negative.unlink()
(EVIDENCE/'negative-control.log').write_text(r.stdout+r.stderr)
assert r.returncode!=0 and 'is false' in r.stdout+r.stderr,'Negative control failed'
for n in order:assert hashlib.sha256(sources[n].read_bytes()).hexdigest()==source_hashes[n],n
record={'status':'passed','toolchain':version.strip(),'upstream_modules':len(entries),'compiled_modules':len(order),
    'axiom_reports':len(expected),'allowed_axioms':sorted(allowed),'dependency_count':len(manifest['packages']),
    'kernel_prefixes':['JSP000476','JSP000476Complete'],'source_sha256':{str(sources[n]):source_hashes[n] for n in order},
    'limits':'Contributor-run compilation and fresh Lean kernel replay; separate NaNoda result is recorded by CI.'}
(EVIDENCE/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
print('All complete-development checks passed.',flush=True)

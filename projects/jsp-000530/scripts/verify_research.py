#!/usr/bin/env python3
"""Compile and replay the existing theorem and the proved research lemmas.

The unresolved target is a proposition definition, not a theorem claimed here.
"""
from pathlib import Path
import datetime, hashlib, json, re, subprocess

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'evidence/research-generated'
OUT.mkdir(parents=True,exist_ok=True)

def run(args, name):
    r=subprocess.run(args,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (OUT/name).write_text(r.stdout)
    if r.returncode:
        raise SystemExit(f'{name}: exit {r.returncode}\n{r.stdout[-5000:]}')
    return r.stdout

version=run(['lake','env','lean','--version'],'lean-version.txt')
assert 'version 4.34.0' in version,version
deps=json.loads((ROOT/'lake-manifest.json').read_text())['packages']
for pkg in deps:
    actual=subprocess.check_output(['git','-C',str(ROOT/'.lake/packages'/pkg['name']),
                                    'rev-parse','HEAD'],text=True).strip()
    assert actual==pkg['rev'],(pkg['name'],actual,pkg['rev'])

(ROOT/'.lake/build/lib/lean').mkdir(parents=True,exist_ok=True)
for module in ['JSP000530','JSP000530Research']:
    run(['lake','env','lean','-DwarningAsError=true','-j1','-M10000','-o',
         f'.lake/build/lib/lean/{module}.olean',f'./{module}.lean'],f'build-{module}.log')
    run(['lake','env','leanchecker','--verbose',module],f'kernel-{module}.log')
    print('Compiled and replayed:',module,flush=True)

targets=[]
for source in ['Audit.lean','AuditResearch.lean']:
    log=run(['lake','env','lean','-DwarningAsError=true','./'+source],source+'.log')
    names=re.findall(r'^#print axioms (\S+)',(ROOT/source).read_text(),re.M)
    for name in names:
        m=re.search("'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",log)
        if m:
            assert {x.strip() for x in m[1].split(',') if x.strip()} <= {
                'propext','Classical.choice','Quot.sound'},(name,m[1])
        else:
            assert "'"+name+"' does not depend on any axioms" in log,name
    targets.extend(names)

negative=ROOT/'NegativeResearch.lean'
try:
    negative.write_text('import JSP000530Research\nexample : (2 : Nat) + 2 = 5 := by decide\n')
    r=subprocess.run(['lake','env','lean','./NegativeResearch.lean'],cwd=ROOT,
                     stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (OUT/'negative.log').write_text(r.stdout)
    assert r.returncode!=0 and 'false' in r.stdout.lower(),r.stdout
finally:
    negative.unlink(missing_ok=True)

files=['JSP000530.lean','JSP000530Research.lean','Audit.lean','AuditResearch.lean',
       'lean-toolchain','lakefile.lean','lake-manifest.json','scripts/verify_research.py',
       'research/perturbation_check.py']
report={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'repository_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        'verified_modules':['JSP000530','JSP000530Research'],
        'audited_targets':targets,'dependency_count':len(deps),
        'source_sha256':{f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files},
        'scope':'Two-axis result and proved research reductions only; no complete proof of the remaining uniform improvement or general-position targets.'}
(OUT/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':'PASS','audited_targets':len(targets),
                  'dependencies':len(deps),'scope':report['scope']},indent=2),flush=True)

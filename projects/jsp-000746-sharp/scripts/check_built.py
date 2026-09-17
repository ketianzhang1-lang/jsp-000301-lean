#!/usr/bin/env python3
"""Replay compiled modules, audit targets and check the exact dependency revisions.

Run verify.sh for source compilation plus these checks. This script alone checks
the existing compiled modules and does not assert that they were freshly built.
"""
from pathlib import Path
import subprocess,json,re,hashlib,datetime
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'evidence/generated';OUT.mkdir(parents=True,exist_ok=True)
def run(args,name,expected=0):
    result=subprocess.run(args,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (OUT/name).write_text(result.stdout)
    if result.returncode!=expected:
        raise SystemExit(f"{name}: exit {result.returncode}\n{result.stdout[-6000:]}")
    return result.stdout
version=run(['lake','env','lean','--version'],'version.txt')
assert 'version 4.34.0' in version,version
for pkg in json.loads((ROOT/'lake-manifest.json').read_text())['packages']:
    actual=subprocess.check_output(['git','-C',str(ROOT/'.lake/packages'/pkg['name']),'rev-parse','HEAD'],text=True).strip()
    assert actual==pkg['rev'],(pkg['name'],actual,pkg['rev'])
modules=json.loads((ROOT/'MODULES.json').read_text())
for module in modules:
    run(['lake','env','leanchecker','--verbose',module],'kernel-'+module+'.log')
    print('Kernel replay passed:',module,flush=True)
audit=run(['lake','env','lean','-DwarningAsError=true','./Audit.lean'],'axioms.log')
targets=re.findall(r'^#print axioms (\S+)',(ROOT/'Audit.lean').read_text(),re.M)
allowed={'propext','Classical.choice','Quot.sound'}
for name in targets:
    m=re.search("'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",audit)
    if m:assert {s.strip() for s in m[1].split(',') if s.strip()}<=allowed,(name,m[1])
    else:assert "'"+name+"' does not depend on any axioms" in audit,name
negative=ROOT/'Negative.lean'
try:
    negative.write_text(f'import {modules[-1]}\nexample : (2 : Nat) + 2 = 5 := by decide\n')
    result=subprocess.run(['lake','env','lean','./Negative.lean'],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (OUT/'negative.log').write_text(result.stdout)
    assert result.returncode!=0 and 'false' in result.stdout,result.stdout
finally:negative.unlink(missing_ok=True)
files=['lean-toolchain','lakefile.lean','lake-manifest.json','UPSTREAM.json','MODULES.json','Audit.lean']
files += [m.replace('.','/')+'.lean' for m in modules]
files += ['scripts/bootstrap.py','scripts/verify.sh','scripts/check_built.py']
hashes={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in files}
commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
report={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'repository_head':commit,'modules':modules,'audited_targets':targets,'allowed_axioms':sorted(allowed),'dependency_count':len(json.loads((ROOT/'lake-manifest.json').read_text())['packages']),'source_sha256':hashes,'scope':'contributor-run kernel replay, axiom/type audits, pinned dependencies and negative control; build logs are recorded separately'}
(OUT/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['status','modules','audited_targets','dependency_count']},indent=2),flush=True)

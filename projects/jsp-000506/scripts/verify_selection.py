"""Rebuild and replay the unchanged complete proof and its selection supplement."""
import hashlib,json,os,re,subprocess
from pathlib import Path
os.chdir(Path(__file__).resolve().parents[1])
os.environ['LEAN_NUM_THREADS']='1'
out=Path('evidence-selection');out.mkdir(exist_ok=True)
pin='2aca2f16eba715d7ad672dfa017481b647c00063'
prefix='projects/jsp-000506'
root=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
paths=subprocess.check_output(['git','-C',str(root),'ls-tree','-r','--name-only',pin,'--',prefix],text=True).splitlines()
bound={}
critical={'lean-toolchain','lake-manifest.json','AUDIT_TARGETS.json','UPSTREAM.json',
          'ORIGINAL_PROOF_SHA256','UPSTREAM_LICENSE','UPSTREAM_LAKE_MANIFEST.json'}
for path in paths:
    if Path(path).suffix in {'.lean','.py','.sh'} or Path(path).name in critical:
        old=subprocess.check_output(['git','-C',str(root),'show',pin+':'+path])
        actual=(root/path).read_bytes()
        if old!=actual:raise SystemExit('Original proof/checking input differs: '+path)
        bound[path]=hashlib.sha256(actual).hexdigest()
new_files=['JSP000506Selection.lean','AuditSelection.lean','SELECTION_TARGETS.json',
           'scripts/verify_selection.py','scripts/verify_selection_nanoda.sh']
new_hashes={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in new_files}
def run(args,name):
    with (out/name).open('w') as log:r=subprocess.run(args,stdout=log,stderr=subprocess.STDOUT)
    if r.returncode:
        print((out/name).read_text()[-20000:],flush=True)
        raise SystemExit('Failed: '+' '.join(args))
    print('Passed: '+' '.join(args),flush=True)
run(['bash','scripts/verify.sh'],'original-verification.log')
run(['lake','env','lean','-DwarningAsError=true','-j1','-M12000','-o',
     '.lake/build/lib/lean/JSP000506Selection.olean','JSP000506Selection.lean'],'selection-build.log')
run(['lake','env','leanchecker','--verbose','JSP000506Selection'],'selection-kernel.log')
run(['lake','env','lean','-DwarningAsError=true','AuditSelection.lean'],'axioms.log')
targets=re.findall(r'^#print axioms (\S+)',Path('AuditSelection.lean').read_text(),re.M)
new=['JSP000506.'+n for n in re.findall(r'^theorem (\w+)',Path('JSP000506Selection.lean').read_text(),re.M)]
original=json.loads(Path('AUDIT_TARGETS.json').read_text())
if len(new)!=11 or len(targets)!=60 or len(set(targets))!=60 or targets!=original+new:
    raise SystemExit('Unexpected audit coverage')
if json.loads(Path('SELECTION_TARGETS.json').read_text())!=targets:
    raise SystemExit('Exporter targets differ from audit')
log=(out/'axioms.log').read_text()
for name in targets:
    m=re.search("'"+re.escape(name)+r"' depends on axioms:\s*\[([^]]*)\]",log)
    if m:
        if not {x.strip() for x in m[1].split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'}:
            raise SystemExit('Unpermitted axiom: '+name)
    elif "'"+name+"' does not depend on any axioms" not in log:
        raise SystemExit('Missing axiom report: '+name)
negative=Path('NegativeSelection.lean')
negative.write_text('import JSP000506Selection\nexample : (1 : Nat) = 0 := by decide\n')
try:r=subprocess.run(['lake','env','lean',str(negative)],capture_output=True,text=True)
finally:negative.unlink()
(out/'negative-control.log').write_text(r.stdout+r.stderr)
if r.returncode==0 or 'is false' not in r.stdout+r.stderr:raise SystemExit('Wrong negative-control outcome')
for path,digest in bound.items():
    if hashlib.sha256((root/path).read_bytes()).hexdigest()!=digest:raise SystemExit('Original input changed: '+path)
for path,digest in new_hashes.items():
    if hashlib.sha256(Path(path).read_bytes()).hexdigest()!=digest:raise SystemExit('New input changed: '+path)
record={'status':'passed','original_proof_commit':pin,
        'verification_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
        'original_input_sha256':bound,'supplement_input_sha256':new_hashes,'targets':targets,
        'new_theorems':new,'allowed_axioms':['propext','Classical.choice','Quot.sound'],
        'limits':'Contributor-run verification with cached pinned Mathlib; not independent human review.'}
(out/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
print('Original and supplementary compilation, kernel replay, 60 axiom reports and negative controls passed.',flush=True)

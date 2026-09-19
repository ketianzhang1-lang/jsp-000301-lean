"""Build and replay the full original submission and its new supplement."""
import hashlib,json,os,re,subprocess
from pathlib import Path
os.chdir(Path(__file__).resolve().parents[1])
os.environ['LEAN_NUM_THREADS']='1'
out=Path('evidence/supplement');out.mkdir(parents=True,exist_ok=True)
module='JSP000897Stability'
pin='914c6fa28200985d6409b5b34588b9f5c4a87d00'
prefix='projects/jsp-000897'
root=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
paths=subprocess.check_output(['git','-C',str(root),'ls-tree','-r','--name-only',pin,'--',prefix],text=True).splitlines()
bound={}
for path in paths:
    if path.endswith('.lean') or Path(path).name in ['lean-toolchain','lake-manifest.json']:
        old=subprocess.check_output(['git','-C',str(root),'show',pin+':'+path])
        actual=(root/path).read_bytes()
        if old!=actual:raise SystemExit('Original source/configuration differs: '+path)
        bound[path]=hashlib.sha256(actual).hexdigest()
def run(args,name):
    with (out/name).open('w') as f:result=subprocess.run(args,stdout=f,stderr=subprocess.STDOUT)
    if result.returncode:
        print((out/name).read_text()[-15000:],flush=True)
        raise SystemExit('Failed: '+' '.join(args))
    print('Passed: '+' '.join(args),flush=True)
run(['bash','scripts/verify.sh'],'original-verification.log')
run(['lake','env','lean','-DwarningAsError=true','-j1','-M10000','-o','.lake/build/lib/lean/'+module+'.olean',module+'.lean'],'supplement-build.log')
run(['lake','env','leanchecker','--verbose',module],'supplement-kernel.log')
run(['lake','env','lean','-DwarningAsError=true','AuditSupplement.lean'],'axioms.log')
targets=re.findall(r'^#print axioms (\S+)',Path('AuditSupplement.lean').read_text(),re.M)
if len(targets)!=15 or len(set(targets))!=15:raise SystemExit('Unexpected audit targets')
log=(out/'axioms.log').read_text()
for name in targets:
    m=re.search("'"+re.escape(name)+r"' depends on axioms:\s*\[([^]]*)\]",log)
    if m:
        if not {x.strip() for x in m[1].split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'}:raise SystemExit('Unpermitted axiom: '+name)
    elif "'"+name+"' does not depend on any axioms" not in log:raise SystemExit('Missing target: '+name)
negative=Path('NegativeSupplement.lean');negative.write_text('import '+module+'\nexample : (1 : Nat) = 0 := by decide\n')
try: result=subprocess.run(['lake','env','lean',str(negative)],capture_output=True,text=True)
finally: negative.unlink()
negative_log=result.stdout+result.stderr
(out/'negative-control.log').write_text(negative_log)
if result.returncode==0 or 'is false' not in negative_log:raise SystemExit('Unexpected negative-control result')
for path,digest in bound.items():
    if hashlib.sha256((root/path).read_bytes()).hexdigest()!=digest:raise SystemExit('Source changed during checking: '+path)
record={'status':'passed','original_proof_commit':pin,'verification_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'original_source_sha256':bound,'supplement_sha256':hashlib.sha256(Path(module+'.lean').read_bytes()).hexdigest(),'targets':targets,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'limits':'Contributor-run verification with cached pinned Mathlib; not independent human review.'}
(out/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
print('Original and supplementary compilation, replay, '+str(len(targets))+' axiom reports and negative controls passed.',flush=True)

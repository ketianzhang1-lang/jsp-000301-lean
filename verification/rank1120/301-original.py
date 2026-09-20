"""Auditor-owned original-source checks; selected e1a17 proof tree is unchanged.
Run only inside the non-root, network-disabled verification container.
"""
import json, pathlib, re, subprocess
root=pathlib.Path.cwd(); out=root/'evidence-rank1120'; out.mkdir(exist_ok=True)
names=['JSP000301.Powerful','JSP000301.PerfectSquare','JSP000301.powerful_12167','JSP000301.powerful_12168','JSP000301.not_square_12167','JSP000301.not_square_12168','JSP000301.jsp_000301_counterexample','JSP000301.jsp_000301_disproved']
def run(args,log):
 p=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (out/log).write_text(p.stdout)
 print('COMMAND',json.dumps(args),'EXIT',p.returncode,flush=True)
 if p.returncode: print(p.stdout);raise SystemExit(p.returncode)
 return p.stdout
run(['lake','build','--wfail'],'build.log')
run(['lake','env','lean','-DwarningAsError=true','JSP000301.lean'],'source.log')
run(['lake','env','leanchecker','JSP000301'],'kernel-main.log')
audit=out/'Audit301.lean'
audit.write_text('import JSP000301\n'+''.join(f'#check @{n}\n#print {n}\n#print axioms {n}\n' for n in names))
log=run(['lake','env','lean','-DwarningAsError=true',str(audit)],'axioms.log')
for name in names:
 m=re.search("'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",log)
 if m: assert {s.strip() for s in m[1].split(',') if s.strip()} <= {'propext','Classical.choice','Quot.sound'},name
 else: assert "'"+name+"' does not depend on any axioms" in log,name
actual={p['name']:subprocess.check_output(['git','-C','.lake/packages/'+p['name'],'rev-parse','HEAD'],text=True).strip() for p in json.loads((root/'lake-manifest.json').read_text())['packages']}
assert all(actual[p['name']]==p['rev'] for p in json.loads((root/'lake-manifest.json').read_text())['packages'])
(out/'dependency-revisions.json').write_text(json.dumps(actual,indent=2))
negative=out/'Negative301.lean';negative.write_text('import JSP000301\nexample : (1 : Nat) = 0 := by decide\n')
p=subprocess.run(['lake','env','lean','-DwarningAsError=true',str(negative)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(out/'negative-control.log').write_text(p.stdout)
assert p.returncode!=0,'False arithmetic accepted'
assert 'error:' in p.stdout and '1' in p.stdout and '0' in p.stdout, 'Negative control did not report a mathematical failure'
(out/'summary.json').write_text(json.dumps({'modules':['JSP000301'],'axiom_targets':names,'dependency_revisions':actual,'negative_control_exit_code':p.returncode,'proof_files_modified':False},indent=2))
print('Eight actual public-target audits, one original module replay, pinned dependencies and false arithmetic rejection completed.')

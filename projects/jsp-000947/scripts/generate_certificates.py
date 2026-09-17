from pathlib import Path
import json
p=Path(__file__).resolve().parents[1]
levels=[{'d': 1, 'lo': 0, 'hi': 7, 'primes': [2], 'remaining': [1, 2, 3, 5]}, {'d': 3, 'lo': 7, 'hi': 21, 'primes': [2], 'remaining': [9]}, {'d': 15, 'lo': 21, 'hi': 1035, 'primes': [11, 19, 13, 17], 'remaining': [], 'base': 2, 'depth': 7}, {'d': 165, 'lo': 1035, 'hi': 4109, 'primes': [13, 19], 'remaining': [], 'base': 7, 'depth': 5}, {'d': 2145, 'lo': 4109, 'hi': 262163, 'primes': [19, 43, 7, 23], 'remaining': [], 'base': 2, 'depth': 7}, {'d': 40755, 'lo': 262163, 'hi': 268435485, 'primes': [29, 37, 2, 17, 23, 53, 47, 71, 107], 'remaining': [], 'base': 7, 'depth': 13}, {'d': 1181895, 'lo': 268435485, 'hi': 68719476773, 'primes': [37, 53, 61, 59, 67, 47, 23, 17, 71, 101, 7], 'remaining': [], 'base': 228, 'depth': 16}, {'d': 43730115, 'lo': 68719476773, 'hi': 17592186044416, 'primes': [53, 59, 61, 67, 83, 71, 23, 17, 41, 47, 101, 109, 631], 'remaining': [], 'base': 1572, 'depth': 19}]
rows={}
for q in set(sum([x["primes"] for x in levels[2:]], [])):
 a=[0]*q
 for k in range(1,44):
  r=pow(2,k,q)
  if a[r]==0: a[r]=k
 rows[str(q)]=a
data={"levels":levels,"rows":rows}
s='import JSP000947\n\nnamespace JSP000947\n\n'
used=sorted(set(sum([x['primes'] for x in data['levels'][2:]],[])))
for q in used:
 a=data['rows'][str(q)]
 s+=f'def row{q} : ℕ × Array ℕ := ({q}, #['+', '.join(map(str,a))+'])\n\n'
for i,x in enumerate(data['levels'][2:],2):
 s+=f'def rows{i} : List (ℕ × Array ℕ) := ['+', '.join('row'+str(q) for q in x['primes'])+']\n\n'
(p/'Tables.lean').write_text(s+'end JSP000947\n')
for i,x in enumerate(data['levels'][2:],2):
 base=x['base'];depth=x['depth'];chunk=min(10,depth)
 f=f'(fun t => passes rows{i} {x["hi"]} ({x["d"]} * t))'
 s='import Tables\n\nnamespace JSP000947\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n'
 names=[]
 for j,start in enumerate(range(base,base+2**depth,2**chunk)):
  name=f'c{i}_{chunk}_{j}';names.append((name,start))
  s+=f'theorem {name} : checkTree {f} {chunk} {start} = true := by\n  decide +kernel\n\n'
 for dep in range(chunk,depth):
  nextnames=[]
  for j in range(len(names)//2):
   name=f'c{i}_{dep+1}_{j}';start=names[2*j][1];nextnames.append((name,start))
   s+=f'theorem {name} : checkTree {f} {dep+1} {start} = true :=\n  checkTree_join {dep} {start} {names[2*j][0]} {names[2*j+1][0]}\n\n'
  names=nextnames
 s+=f'theorem certificate{i} : checkTree {f} {depth} {base} = true :=\n  {names[0][0]}\n\nend JSP000947\n'
 (p/f'Certificate{i}.lean').write_text(s)
(p/'Certificates.lean').write_text(''.join(f'import Certificate{i}\n' for i in range(2,8)))

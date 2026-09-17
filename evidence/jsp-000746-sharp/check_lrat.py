#!/usr/bin/env python3
"""Independent RUP-only LRAT checker for the attributed 18-vertex certificate.

The checker rejects every RAT hint. It first reconstructs all graph clauses from
scratch, so proving an unrelated Boolean formula cannot pass this check.
Standard library only. It is not an independently verified implementation of
Lean's type theory, and does not replace human statement/attribution review.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
from pathlib import Path

class InvalidCertificate(ValueError):
    pass

def expected_graph_cnf(n: int = 18) -> list[tuple[int,...]]:
    vertices = range(1,n+1)
    variable = {pair: i+1 for i,pair in enumerate(itertools.combinations(vertices,2))}
    triangles = [tuple(-variable[e] for e in itertools.combinations(t,2))
                 for t in itertools.combinations(vertices,3)]
    schur = [tuple(variable[e] for e in itertools.combinations((a,b,a+b),2))
             for a in vertices for b in range(a+1,n+1) if a+b<=n]
    return triangles+schur

def read_cnf(text: str) -> list[tuple[int,...]]:
    clauses=[]; header=None; pending=[]
    for line in text.splitlines():
        words=line.split()
        if not words or words[0]=='c': continue
        if words[0]=='p':
            if header is not None or len(words)!=4 or words[1]!='cnf':
                raise InvalidCertificate('Bad DIMACS header')
            header=(int(words[2]),int(words[3])); continue
        for word in words:
            value=int(word)
            if value==0:
                clauses.append(tuple(pending));pending=[]
            else: pending.append(value)
    if pending or header!=(153,888):
        raise InvalidCertificate('Unexpected dimensions or unterminated clause')
    if clauses!=expected_graph_cnf():
        raise InvalidCertificate('CNF does not equal the independently reconstructed graph encoding')
    return clauses

def check_proof(initial: list[tuple[int,...]], text: str) -> dict:
    database={i+1:c for i,c in enumerate(initial)}
    last_add=len(initial); additions=0; deleted=0; hint_checks=0; empty=False
    for lineno,line in enumerate(text.splitlines(),1):
        words=line.split()
        if not words or words[0]=='c': continue
        label=int(words[0])
        if len(words)>1 and words[1]=='d':
            ids=list(map(int,words[2:]))
            if not ids or ids[-1]!=0 or 0 in ids[:-1]:
                raise InvalidCertificate(f'Bad deletion at line {lineno}')
            for key in ids[:-1]:
                if key not in database:
                    raise InvalidCertificate(f'Deletion of missing clause {key}')
                del database[key];deleted+=1
            continue
        values=list(map(int,words[1:]))
        try: split=values.index(0)
        except ValueError as exc: raise InvalidCertificate('Missing clause terminator') from exc
        clause=tuple(values[:split]); hints=values[split+1:]
        if label<=last_add or not hints or hints[-1]!=0 or any(h<=0 for h in hints[:-1]):
            raise InvalidCertificate(f'Bad addition / non-RUP proof at line {lineno}')
        if any(abs(l)>153 for l in clause):
            raise InvalidCertificate('Out-of-range variable')
        assignment: dict[int,bool]={}; conflict=False
        for literal in clause:
            key=abs(literal); value=literal<0  # negate the proposed clause
            if key in assignment and assignment[key]!=value:
                conflict=True
            assignment[key]=value
        for hint in hints[:-1]:
            if hint not in database:
                raise InvalidCertificate(f'Missing hinted clause {hint} at line {lineno}')
            if conflict: continue
            hint_checks+=1
            current=database[hint]; unassigned=set(); satisfied=False
            for literal in current:
                key=abs(literal)
                if key not in assignment: unassigned.add(literal)
                elif assignment[key]==(literal>0): satisfied=True
            if satisfied or len(unassigned)>1:
                raise InvalidCertificate(f'Hint is not unit/conflicting at line {lineno}')
            if not unassigned:
                conflict=True
            else:
                literal=next(iter(unassigned)); assignment[abs(literal)]=literal>0
        if not conflict:
            raise InvalidCertificate(f'RUP contradiction not reached at line {lineno}')
        database[label]=clause;last_add=label;additions+=1
        if not clause: empty=True
    if not empty:
        raise InvalidCertificate('No empty clause derived')
    return {'initial_variables':153,'initial_clauses':len(initial),
            'triangle_clauses':816,'schur_clauses':72,
            'rup_additions':additions,'deleted_clauses':deleted,
            'unit_or_conflict_hints_checked':hint_checks,
            'empty_clause_derived':True,'last_addition_id':last_add}

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory',type=Path,nargs='?',default=Path(__file__).parent)
    args=parser.parse_args()
    cnf_path=args.directory/'Certificate.cnf'; proof_path=args.directory/'Certificate.lrat'
    cnf_text=cnf_path.read_text();proof_text=proof_path.read_text()
    initial=read_cnf(cnf_text);report=check_proof(initial,proof_text)
    # Removing the final derivation's evidence must be rejected.
    bad=proof_text.splitlines();bad[-1]=f"{report['last_addition_id']} 0 0"
    try: check_proof(initial,'\n'.join(bad))
    except InvalidCertificate: pass
    else: raise AssertionError('Missing-hints negative control unexpectedly accepted')
    # Altering a graph clause must be rejected before any proof is checked.
    try: read_cnf(cnf_text.replace('-1 -2 -18 0','1 -2 -18 0',1))
    except InvalidCertificate: pass
    else: raise AssertionError('Wrong-encoding negative control unexpectedly accepted')
    report['negative_controls_rejected']=2
    report['sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (cnf_path,proof_path)}
    Path(__file__).with_name('lrat-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2)); print('INDEPENDENT GRAPH ENCODING AND RUP CHECKS PASSED')

if __name__=='__main__': main()

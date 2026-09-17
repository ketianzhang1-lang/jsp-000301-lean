#!/usr/bin/env python3
"""Exact integer diagnostics for the original and quadratically bent axes.

The bent points are scaled by denominator D, which preserves all incidence
properties and distance-equality counts. Finite experiments are not a proof of
an asymptotic statement. No floating-point tolerance is used.
"""
from itertools import combinations
from pathlib import Path
import json

def orientation(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])

def circle_det(a, b, c, d):
    def row(q):
        return q[0]-a[0], q[1]-a[1], q[0]**2+q[1]**2-a[0]**2-a[1]**2
    x,y,z=row(b); u,v,w=row(c); r,s,t=row(d)
    return x*(v*t-w*s)-y*(u*t-w*r)+z*(u*s-v*r)

def inspect(points):
    assert len(set(points))==len(points)
    triples=sum(orientation(*q)==0 for q in combinations(points,3))
    circles=sum(circle_det(*q)==0 and any(orientation(*tri)!=0
                for tri in combinations(q,3)) for q in combinations(points,4))
    counts=[len({(p[0]-q[0])**2+(p[1]-q[1])**2
                 for q in points if p!=q}) for p in points]
    return {'n':len(points),'collinear_triples':triples,
            'concyclic_quadruples':circles,'min_pinned_distances':min(counts),
            'max_pinned_distances':max(counts)}

def run():
    D=10000
    results=[]
    for m in [2,3,4,6,8]:
        xs=[s*2*(i+1) for i in range(m) for s in [-1,1]]
        ys=[s*(2*i+1) for i in range(m) for s in [-1,1]]
        original=[(x,0) for x in xs]+[(0,y) for y in ys]
        bent=[(D*x,x*x) for x in xs]+[(y*y,D*y) for y in ys]
        results.append({'m':m,'t_denominator':D,
                        'original':inspect(original),'bent':inspect(bent)})
    return {'arithmetic':'exact integers','status':'finite diagnostics only',
            'results':results}

if __name__=='__main__':
    result=run()
    output=Path(__file__).with_name('perturbation-results.json')
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

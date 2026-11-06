"""Exact Laurent normalization and determinant-cleared lower-germ elimination.

Exploratory until a closing ideal certificate is obtained.  No specialization
of Hecke eigenvalues or exponential parameters is made.
"""
from pathlib import Path
import json
import math
import sys
import sympy as s
from sympy.polys.fields import field

src=Path(sys.argv[1] if len(sys.argv)>1 else '/tmp/level26_root_widehigher2_mmm.json')
data=json.loads(src.read_text())
K,x,y,z,w,a,b=field('x,y,z,w,a,b',s.QQ)
rows=[]
for rr in data['equations']:
    row={}
    for j,v in rr.items():
        f=K.from_expr(s.sympify(v)); assert len(f.denom.terms())==1
        dp,dc=f.denom.terms()[0];terms={}
        for p,c in f.numer.terms():
            e=[pi-di for pi,di in zip(p,dp)]
            e[1]-=e[4];e[3]-=e[5]
            assert e[1]%2==e[3]%2==0
            e[1]//=2;e[3]//=2
            terms[tuple(e)]=c/dc
        row[int(j)]=terms
    mins=[min(p[i] for terms in row.values() for p in terms) for i in range(6)]
    assert mins[4]>=0 and mins[5]>=0
    # Only exponential monomials can be divided away.
    mins[4]=mins[5]=0
    row={j:{tuple(pi-mi for pi,mi in zip(p,mins)):c for p,c in terms.items()} for j,terms in row.items()}
    rows.append(row)
unique={}
for row in rows:
    first=next(c for j in sorted(row) for p,c in sorted(row[j].items()))
    rr={j:{p:c/first for p,c in terms.items()} for j,terms in row.items()}
    key=tuple((j,tuple(sorted(ts.items()))) for j,ts in sorted(rr.items()))
    unique[key]=rr
rows=list(unique.values())
rows.sort(key=lambda r:(sum(len(v) for v in r.values()),len(r)))
names=['x','Y','z','W','A','B']
def emit(terms):
    return '+'.join('('+str(c)+')'+''.join('*'+v+('^'+str(e) if e!=1 else '') for v,e in zip(names,p) if e) for p,c in terms.items()) or '0'
out='Alarm(45); SetSeed(1);\nP<x,Y,z,W,A,B>:=PolynomialRing(Rationals(),6,"grevlex");\n'
out+='rows:=[P|];\n'
# Sequence of sequences, followed by an exact rectangular matrix.
out=out.replace('rows:=[P|];','rows:=[* *];')
for r in rows:out+='Append(~rows,[P|'+','.join(emit(r.get(j,{})) for j in range(6))+']);\n'
code=''.join('p' if sg==1 else 'm' for sg in data['signs'])
out+=(Path(__file__).with_name('level26_negative_poles_backend.m')).read_text().replace('__CODE__',code)
dst=Path('/tmp/level26_negative_poles_'+code+'.m');dst.write_text(out)
print('EXPORTED',len(rows),'rows',len(out),'bytes',dst,flush=True)

"""Verify the global leading/first-source rank on the nonzero torus.
This leaves simple poles at the exceptional Taylor scalar s=k untouched.
"""
from pathlib import Path
import json,sys
from sympy import symbols,sympify,cancel,Poly,groebner
x,y,z,w,a,b,A,Y=symbols('x y z w a b A Y')
code=sys.argv[1]
d=json.loads(Path('/tmp/level26_prime5_rows_390_'+code+'.json').read_text())
assert len(d['free'])==2
L=[[sympify(v) for v in r] for r in d['lead']]
J=[[sympify(v) for v in r] for r in d['jet']]
def mono(v):
 if not v or v.has(a,b):return False
 n,d=cancel(v).as_numer_denom()
 return len(Poly(n,x,y,z,w).terms())==len(Poly(d,x,y,z,w).terms())==1
i,j=next((i,j) for i,r in enumerate(J) for j in range(2) if mono(r[j]) and not r[1-j])
P=[];ids=[]
for ri,r in enumerate(L+J):
 f=cancel(r[1-j].subs(a,A/y)).as_numer_denom()[0]
 if not f:continue
 pol=Poly(f,x,y,z,w,A,b);mins=[min(p[i] for p,c in pol.terms()) for i in range(4)]
 f=cancel(f/(x**mins[0]*y**mins[1]*z**mins[2]*w**mins[3]));pol=Poly(f,y)
 assert all(p[0]%2==0 for p,c in pol.terms())
 f=sum(c*Y**(p[0]//2) for p,c in pol.terms());assert not f.has(b,w,z,y)
 f=Poly(f,A,Y,x).monic().as_expr()
 if f not in P:P.append(f);ids.append(ri)
G=groebner(P,A,Y,x,method='f5b')
assert G.reduce(x)[1]==0
out={'signs':d['signs'],'jet_monomial_pivot':[i,j,str(J[i][j])],
 'remaining_column':1-j,'scalar_rows':ids,'polynomials':[str(p) for p in P],
 'groebner_basis':[str(p) for p in G],'x_remainder':'0',
 'claim':'Full rank for leading plus first-source equations at every nonzero exponential tuple; simple weight-k poles not excluded'}
Path('/tmp/level26_prime5_rank_'+code+'.json').write_text(json.dumps(out,indent=2)+'\n')
print('N26_PRIME5_GLOBAL_FIRST_SOURCE_RANK_VERIFIED',code,list(G),flush=True)

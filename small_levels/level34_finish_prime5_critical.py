"""Exact critical-line rank certificate after the prime5 first-Taylor rows.
Works from exported exact reduced rows; does not itself establish continuation.
"""
import json,sys
from pathlib import Path
from sympy import symbols,sympify,cancel,factor,Poly,groebner
x,y,z,w,a,b,A,Y=symbols('x y z w a b A Y')
code=sys.argv[1];data=json.loads(Path('/tmp/level34_finish_prime5_rows_510_'+code+'.json').read_text());eta,sigma,tau=data['signs'];assert len(data['free'])==3
L=[[cancel(sympify(v).subs(x,-sigma)) for v in r] for r in data['lead']]
J=[[cancel(sympify(v).subs(x,-sigma)) for v in r] for r in data['jet']]
def mono(v):
 if not v:return False
 n,d=cancel(v).as_numer_denom()
 return (not v.has(a,b) and len(Poly(n,y,z,w).terms())==len(Poly(d,y,z,w).terms())==1)
zcol=next(i for i in range(3) if all(r[i]==0 for r in J));others=[i for i in range(3) if i!=zcol]
jidx,jcol=next((i,j) for i,r in enumerate(J) for j in others if mono(r[j]));fcol=next(i for i in others if i!=jcol)
v=[0,0,0];v[fcol]=1;v[jcol]=cancel(-J[jidx][fcol]/J[jidx][jcol]);lidx=next(i for i,r in enumerate(L) if mono(r[zcol]));v[zcol]=cancel(-sum(L[lidx][j]*v[j] for j in others)/L[lidx][zcol])
P=[];ids=[]
for i,r in enumerate(L+J):
 p=cancel(sum(r[j]*v[j] for j in range(3))).subs(a,A/y);nu=cancel(p).as_numer_denom()[0]
 if not nu:continue
 pol=Poly(nu,y);assert all(e[0]%2==0 for e,c in pol.terms());p2=sum(c*Y**(e[0]//2) for e,c in pol.terms());p2=Poly(p2,b,w,z,A,Y).monic().as_expr()
 if p2 not in P:P.append(p2);ids.append(i)
G=groebner(P,b,w,z,A,Y,method='f5b');print('critical',code,'pivots',lidx,zcol,jidx,jcol,'remaining',fcol,'polys',len(P),'basis',[factor(p) for p in G],flush=True)
assert list(G)==[1]
Path('/tmp/level34_finish_prime5_critical_'+code+'.json').write_text(json.dumps({'signs':data['signs'],'leading_pivot':[lidx,zcol,str(L[lidx][zcol])],'jet_pivot':[jidx,jcol,str(J[jidx][jcol])],'free_column':fcol,'scalar_rows':ids,'polynomials':[str(p) for p in P],'groebner_basis':['1']},indent=2)+'\n')
print('N34_PRIME5_CRITICAL_FULL_RANK_VERIFIED',code)

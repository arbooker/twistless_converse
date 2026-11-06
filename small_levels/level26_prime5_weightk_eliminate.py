"""Explore leading-only exceptional-pole equations over Q(x,Y).
No positivity or all-weight conclusion is asserted by this computation.
"""
from pathlib import Path
import json,sys
import sympy as S
x,y,z,w,a,b,A,B,Y,W,t=S.symbols('x y z w a b A B Y W t')
code=sys.argv[1] if len(sys.argv)>1 else 'mmm'
d=json.loads((Path(__file__).parent/'level26_prime5_wide_certificate.json').read_text())['cases'][code]['rows']
P=[]
for row in d['lead']:
 e=S.cancel((S.sympify(row[0])+t*S.sympify(row[1])).subs({a:A/y,b:B/w}))
 p=S.Poly(e.as_numer_denom()[0],x,y,z,w,A,B,t)
 mins=[min(pw[j] for pw,co in p.terms()) for j in range(4)]
 e=S.cancel(p.as_expr()/S.prod(v**n for v,n in zip([x,y,z,w],mins)))
 q=S.Poly(e,y);assert all(pw[0]%2==0 for pw,co in q.terms())
 e=S.expand(sum(co*Y**(pw[0]//2) for pw,co in q.terms()))
 q=S.Poly(e,w);assert all(pw[0]%2==0 for pw,co in q.terms())
 e=S.expand(sum(co*W**(pw[0]//2) for pw,co in q.terms()))
 e=S.Poly(e,A,t,B,z,W,x,Y).monic().as_expr()
 if e not in P:P.append(e)
print('leading chart equations',len(P),flush=True)
Path('/tmp/level26_prime5_weightk_polys_'+code+'.json').write_text(json.dumps([str(p) for p in P],indent=2))
if 'magma' in sys.argv:
 def fmt(e):return str(e).replace('**','^')
 Path('/tmp/level26_prime5_weightk_eliminate_'+code+'.m').write_text('SetNthreads(1);\nQ:=Rationals();\nF<x,Y>:=FunctionField(Q,2);\nR<A,t,B,z,W>:=PolynomialRing(F,5);\nI:=ideal<R|'+','.join(fmt(p) for p in P)+'>;\ntime G:=GroebnerBasis(I);\nG;\nquit;\n')
else:
 G=S.groebner(P,A,t,B,z,W,domain=S.QQ.frac_field(x,Y),method='f5b')
 print('basis length',len(G),flush=True)
 Path('/tmp/level26_prime5_weightk_eliminants_'+code+'.json').write_text(json.dumps([str(p) for p in G],indent=2))
 for p in G:
  if not p.has(A,t,B):print(S.factor(p),flush=True)

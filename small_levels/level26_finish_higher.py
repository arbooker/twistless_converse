"""Exploratory exact higher Taylor compatibility on Q78.
Normalized principal coefficients assume all Taylor falling factors used are nonzero.
This is NOT a pole exclusion certificate at s-k in the nonnegative integers.
N26_H integer specializes 2^(s-k/2),3^(s-k/2),13^(s-k/2).
"""
from pathlib import Path
import os
src=Path(__file__).with_name('level26_finish_first_consistency.py').read_text()
exec(src[:src.index('kernels=[];sources=[]')].replace('assert len(free)==2','assert len(free)>=1'))
from math import factorial
from sympy import factor, gcd as polygcd
h=os.environ.get('N26_H')
if h is not None:
 hh=int(h)
 def specialize(v):
  def pol(p):
   return sum((K(cf)*K(Fraction(2)**(hh*pw[0])*Fraction(3)**(hh*pw[1])*Fraction(13)**(hh*pw[2]))*a**pw[3] for pw,cf in p.terms()),K.zero)
  return pol(v.numer)/pol(v.denom)
else:
 def specialize(v):return v

def sh(v,n):return specialize(shift(v,n))
def addvec(v,w,c=K.one):
 for j,t in w.items():
  v[j]=v.get(j,K.zero)+c*t
  if not v[j]:del v[j]
 return v
prev=[];equations=[]
for n in range(int(os.environ.get('N26_ORDERS','3'))+1):
 bs=[]
 for row,lab in original:
  vec={}
  if lab[0]=='g':
   _,A,B,C,D,mu,j=lab;den=C*j+D*Q;dest=Q*(A*j+B*Q)//den%Q;det=A*D-B*C
   leading=mu*mon(Fraction(den*den,det*Q*Q));slope=K(Fraction(C*den,det*Q))
   for m in range(1,n+1):addvec(vec,prev[n-m][dest],sh(leading,n)*slope**m/K(factorial(m)))
  if lab[0]=='F':
   _,q,t=lab;ell=lcm(N,q*q);dest=-(Q*Q//ell)//t
   leading=eta*(-bad2 if q%2==0 else 1)*(-bad13 if q%13==0 else 1)*mon(Fraction(ell*t*t,Q*Q));slope=K(Fraction(ell*t,Q))
   off=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
   for m in range(1,n+1):
    for j in off:addvec(vec,prev[n-m][(j+dest)%Q],sh(leading,n)*slope**m/K(factorial(m)))
  bs.append(vec)
 for rid,val,updates in operations:
  bs[rid]={j:v/sh(val,n) for j,v in bs[rid].items()}
  for rid2,coef in updates:addvec(bs[rid2],bs[rid],-sh(coef,n))
 for rid in zeroids:
  if bs[rid]:equations.append(dict(bs[rid]))
 for row,rid in R:
  eq={n*len(free)+i:sh(row.get(j,K.zero),n) for i,j in enumerate(free) if row.get(j)}
  addvec(eq,bs[rid],-K.one)
  if eq:equations.append(eq)
 vals=[{} for _ in range(Q)]
 for i,j in enumerate(free):vals[j]={n*len(free)+i:K.one}
 for j,row,rid in reversed(piv):
  vals[j]=dict(bs[rid])
  for c,v in row.items():
   if c!=j:addvec(vals[j],vals[c],-sh(v,n))
 prev.append(vals)
 # Exact row reduction with only constant monomial pivots preserves every a specialization.
 todo=[dict(e) for e in equations];piv2=[]
 while True:
  choices=[i for i,r in enumerate(todo) if any(safe(v) for v in r.values())]
  if not choices:break
  ii=min(choices,key=lambda i:len(todo[i]));r=todo.pop(ii)
  j=min(j for j,v in r.items() if safe(v));val=r[j];r={j:v/val for j,v in r.items()};piv2.append((j,r))
  new=[]
  for e in todo:
   if j in e:addvec(e,r,-e[j])
   if e:new.append(e)
  todo=new
 remaining=sorted({j for r in todo for j in r})
 print('order',n,'eqs',len(equations),'monomial pivots',len(piv2),'remaining',remaining,'rows',len(todo),flush=True)
 if h is not None and n>0:
  from sympy import symbols,groebner
  vv=symbols('v:'+str((n+1)*len(free)));aa=symbols('a')
  polys=list(set(sum(c.as_expr()*vv[j] for j,c in e.items()).as_numer_denom()[0] for e in equations))
  for normcol in range(len(free)):
   gb=groebner(polys+[vv[normcol]-1],*vv,aa)
   pure=[factor(g) for g in gb.polys if g.as_expr().free_symbols <= {aa}]
   print('normalized',normcol,'GB length',len(gb.polys),'parameter obstruction',pure,flush=True)

if os.environ.get('N26_EXPORT'):
 import json
 active=sorted({j for e in equations for j in e})
 Path(os.environ['N26_EXPORT']).write_text(json.dumps({'signs':[eta,bad2,bad13], 'Q':Q,'free':free,'active':active,'equations':[{str(j):str(v) for j,v in e.items()} for e in equations]},indent=2))

"""Higher jets for eta-plus q5 branch 9*x^2=4*y^2.
Exact experimental reduction; polynomial exceptional divisors printed.
"""
import sys,time
from pathlib import Path
sys.argv=[sys.argv[0],'1']
base=Path(__file__).parent
src=(base/'level25_finish_firstjet.py').read_text()
exec(src[:src.index('constraints=[]')])
from sympy.polys.fields import field
from sympy import QQ,factor,Poly,gcd as pgcd
from functools import lru_cache
from math import factorial
L,X,Z=field('X,Z',QQ)
@lru_cache(None)
def ev(v,n=0):
 images=[X/2**n,3*X/(2*3**n),Z/5**n,-X-2/X,-3*X/2-2/X]
 if v:
  np={(pw[1]+pw[4])%2 for pw,co in v.numer.terms()}
  dp={(pw[1]+pw[4])%2 for pw,co in v.denom.terms()}
  assert len(np)==1 and np==dp,('sign branch mismatch',v)
 def poly(p):
  ans=L.zero
  for pw,co in p.terms():
   term=L(co)
   for im,e in zip(images,pw):term*=im**e
   ans+=term
  return ans
 return poly(v.numer)/poly(v.denom)
prev=[];allminors=[];determinants=[]
def source(lab,n):
 if n==0:return L.zero
 if lab[0]=='g':
  _,A,B,C,D,mu,j=lab;den=C*j+D*Q;dest=Q*(A*j+B*Q)//den%Q;det=A*D-B*C
  leading=mu*mon(Fraction(den*den,det*Q*Q));slope=L(Fraction(C*den,det*Q))
  return ev(leading,n)*sum((slope**m/factorial(m)*prev[n-m][dest] for m in range(1,n+1)),L.zero)
 if lab[0]=='F':
  _,q,t=lab;ell=lcm(N,q*q);dest=-(Q*Q//ell)//t
  leading=eta*mon(Fraction(ell*t*t,Q*Q));slope=L(Fraction(ell*t,Q))
  off=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
  return ev(leading,n)*sum((slope**m/factorial(m)*sum((prev[n-m][(j+dest)%Q] for j in off),L.zero) for m in range(1,n+1)),L.zero)
 return L.zero
for n in range(4):
 bv=[source(lab,n) for row,lab in original]
 for rid,val,updates in operations:
  bv[rid]/=ev(val,n)
  for rid2,coef in updates:bv[rid2]-=ev(coef,n)*bv[rid]
 matrix=[({i:ev(row.get(c,K.zero),n) for i,c in enumerate(free) if row.get(c,K.zero)},bv[rid],original[rid][1]) for row,rid in R]
 matrix +=[({},bv[rid],original[rid][1]) for rid in zeroids if bv[rid]]
 if n==0:matrix.append(({3:L.one},L.one,('normalize',)))
 basis={};det=L.one;bad=[]
 for rr,bb,lab in sorted(matrix,key=lambda item:len(item[0])):
  rr={j:v for j,v in rr.items() if v}
  while rr:
   j=min(rr)
   if j not in basis:
    val=rr[j];det*=val;basis[j]=({i:v/val for i,v in rr.items()},bb/val);break
   br,bs=basis[j];c=rr[j];bb-=c*bs
   for i,v in br.items():
    rr[i]=rr.get(i,L.zero)-c*v
    if not rr[i]:del rr[i]
  else:
   if bb:bad.append((lab,bb))
 determinants.append(det)
 print('ORDER',n,'RANK',len(basis),'DET',factor(det.as_expr()),'BAD',len(bad),flush=True)
 if bad:
  polys=[]
  for lab,bb in bad:
   p=bb.numer.as_expr();polys.append(p)
  g=polys[0]
  for p in polys[1:]:g=pgcd(g,p)
  print('OBSTRUCTION_GCD',factor(g),flush=True)
  print('FIRST_OBSTRUCTION',bad[0][0],factor(bad[0][1].as_expr()),flush=True)
  break
 assert len(basis)==4
 vals=[L.zero]*4
 for j in sorted(basis,reverse=True):
  row,bb=basis[j];vals[j]=bb-sum((v*vals[i] for i,v in row.items() if i!=j),L.zero)
 w=[L.zero]*Q
 for c,v in zip(free,vals):w[c]=v
 for j,row,rid in reversed(piv):w[j]=bv[rid]-sum((ev(v,n)*w[c] for c,v in row.items() if c!=j),L.zero)
 prev.append(w)

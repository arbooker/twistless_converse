"""Exact higher Taylor jets on the exceptional eta-minus q5 pole branch.
Only normalized residue systems are tested; no modularity is assumed.
"""
import sys,time
from pathlib import Path
from fractions import Fraction
sys.argv=[sys.argv[0],'-1']
base=Path(__file__).parent
exec((base/'level25_finish_augmented.py').read_text())
original=[(dict(row),lab) for row,lab in R]
from functools import lru_cache
from math import factorial
@lru_cache(None)
def ev(v,n=0):
 ims=[Fraction(2)**(1-n),Fraction(3)**(1-n),Fraction(5)**(1-n),Fraction(-1,2),Fraction(-7,3)]
 def poly(p):
  ans=Fraction(0)
  for pw,co in p.terms():
   term=Fraction(int(co.numerator),int(co.denominator))
   for im,e in zip(ims,pw):term*=im**e
   ans+=term
  return ans
 return poly(v.numer)/poly(v.denom)
prev=[]
def source(lab,n):
 if n==0:return Fraction(0)
 if lab[0]=='g':
  _,A,B,C,D,mu,j=lab;den=C*j+D*Q;dest=Q*(A*j+B*Q)//den%Q;det=A*D-B*C
  leading=mu*mon(Fraction(den*den,det*Q*Q));slope=Fraction(C*den,det*Q)
  return ev(leading,n)*sum(slope**m/factorial(m)*prev[n-m][dest] for m in range(1,n+1))
 if lab[0]=='F':
  _,q,t=lab;ell=lcm(N,q*q);dest=-(Q*Q//ell)//t
  leading=eta*mon(Fraction(ell*t*t,Q*Q));slope=Fraction(ell*t,Q)
  off=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
  return ev(leading,n)*sum(slope**m/factorial(m)*sum(prev[n-m][(j+dest)%Q] for j in off) for m in range(1,n+1))
 return Fraction(0)
for n in range(6):
 basis={};bad=[]
 extra=[({120:K.one},('normalize',)),({60:K.one},('firstjet',))] if n==0 else []
 for row,lab in original+extra:
  r={j:ev(v,n) for j,v in row.items()};r={j:v for j,v in r.items() if v};bb=source(lab,n)
  if lab[0]=='normalize':bb=Fraction(1)
  if lab[0]=='firstjet':bb=Fraction(-1,2)
  while r:
   j=min(r)
   if j not in basis:
    val=r[j];basis[j]=({i:v/val for i,v in r.items()},bb/val);break
   row0,b0=basis[j];val=r[j];bb-=val*b0
   for i,v in row0.items():
    r[i]=r.get(i,Fraction(0))-val*v
    if not r[i]:del r[i]
  else:
   if bb:bad.append((lab,bb))
 print('ORDER',n,'RANK',len(basis),'OBSTRUCTIONS',bad[:4],flush=True)
 if bad:
  assert n==3 and len(basis)==Q
  assert any(lab==('R',5) and value==Fraction(-25,2) for lab,value in bad)
  print('N25_MINUS_EXCEPTIONAL_THIRD_JET_PASS',flush=True)
  break
 assert len(basis)==Q
 w=[Fraction(0)]*Q
 for j in sorted(basis,reverse=True):
  row,bb=basis[j];w[j]=bb-sum(v*w[i] for i,v in row.items() if i!=j)
 prev.append(w)
else: raise AssertionError("Expected third-order obstruction missing")

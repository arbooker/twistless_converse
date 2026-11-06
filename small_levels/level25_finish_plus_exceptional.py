"""Exact higher Taylor jets on the exceptional eta-minus q5 pole branch.
Only normalized residue systems are tested; no modularity is assumed.
"""
import sys,time
from pathlib import Path
from fractions import Fraction
sys.argv=[sys.argv[0],'1']
base=Path(__file__).parent
exec((base/'level25_finish_augmented.py').read_text())
original=[(dict(row),lab) for row,lab in R]
from functools import lru_cache
from math import factorial
@lru_cache(None)
def ev(v,n=0):
 ims=[Fraction(2)**(1-n),Fraction(3)**(1-n),Fraction(5)**(1-n),Fraction(-3),Fraction(-4)]
 def poly(p):
  ans=Fraction(0)
  for pw,co in p.terms():
   term=Fraction(int(co.numerator),int(co.denominator))
   for im,e in zip(ims,pw):term*=im**e
   ans+=term
  return ans
 return poly(v.numer)/poly(v.denom)

# One finite block system, so higher pole orders at lower points are
# addressed by its full column rank, rather than assumed away.
from collections import defaultdict
for depth in [1,2,3]:
 basis={};bad=[]
 for n in range(depth+1):
  for row,lab in original:
   rr={n*Q+j:ev(v,n) for j,v in row.items()}
   if lab[0]=='g':
    _,A,B,C,D,mu,j=lab;den=C*j+D*Q;dest=Q*(A*j+B*Q)//den%Q;det=A*D-B*C
    leading=mu*mon(Fraction(den*den,det*Q*Q));slope=Fraction(C*den,det*Q);targets=[dest]
   elif lab[0]=='F':
    _,q,t=lab;ell=lcm(N,q*q);dest=-(Q*Q//ell)//t
    leading=eta*mon(Fraction(ell*t*t,Q*Q));slope=Fraction(ell*t,Q)
    targets=[(a0*(Q//q)+dest)%Q for a0 in range(q) if gcd(a0,q)==1]
   else:targets=[]
   for m in range(1,n+1):
    if targets:
     co=ev(leading,n)*slope**m/factorial(m)
     for j in targets:rr[(n-m)*Q+j]=rr.get((n-m)*Q+j,Fraction(0))-co
   rr={j:v for j,v in rr.items() if v}
   while rr:
    j=min(rr)
    if j not in basis:
     val=rr[j];basis[j]={i:v/val for i,v in rr.items()};break
    br=basis[j];c=rr[j]
    for i,v in br.items():
     rr[i]=rr.get(i,Fraction(0))-c*v
     if not rr[i]:del rr[i]
  print('DEPTH',depth,'LEVEL',n,'BLOCK_RANK',len(basis),flush=True)
 freecols=sorted(set(range((depth+1)*Q))-set(basis))
 print('DEPTH_FREE',depth,freecols,flush=True)
 if not freecols:
  assert depth==2 and len(basis)==450
  print('N25_PLUS_EXCEPTIONAL_FINITE_BLOCK_FULL_RANK_PASS',flush=True);break
else: raise AssertionError("Expected depth-two full rank missing")

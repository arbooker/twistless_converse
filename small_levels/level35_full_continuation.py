"""Exact uniform continuation of all210 additive twists at level35.
Uses the additional G6 invariance proved in level35_modulus6.tex.
Run all32 sign/zero-parameter strata; each pivot is nonidentically zero
on every allowed eigenvalue specialization in its stratum.
"""
from pathlib import Path
from fractions import Fraction
from functools import reduce
from math import gcd,lcm
from sympy.polys.fields import field
from sympy import QQ
import sys,time,json
N=35;Q=210
U=set(range(210))
K,x,y,z,w,a,b=field('x,y,z,w,a,b',QQ);V={2:x,3:y,5:z,7:w}
eta=int(sys.argv[1]) if len(sys.argv)>1 else -1
bad5=int(sys.argv[2]) if len(sys.argv)>2 else -1
bad7=int(sys.argv[3]) if len(sys.argv)>3 else -1
zero2='zero2' in sys.argv;zero3='zero3' in sys.argv
if zero2:a=K.zero
if zero3:b=K.zero
assert all(c in [-1,1] for c in [eta,bad5,bad7])
def norm(g):
 d=reduce(gcd,g);g=tuple(v//d for v in g)
 return tuple(-v for v in g) if next(v for v in g if v)<0 else g
def mul(g,h):
 A,B,C,D=g;E,F,G,H=h
 return norm((A*E+B*G,A*F+B*H,C*E+D*G,C*F+D*H))
def inv(g):A,B,C,D=g;return norm((D,-B,-C,A))
def mon(t):
 t=abs(Fraction(t));num=t.numerator;den=t.denominator;r=K.one
 for p,v in V.items():
  while num%p==0:num//=p;r*=v
  while den%p==0:den//=p;r/=v
 assert num==den==1,(t,num,den)
 return r
def divisors(n):return [d for d in range(1,n+1) if n%d==0]
gens=[((1,1,0,1),1),((1,0,35,1),1),((2,-1,-35,18),1),((0,-1,35,0),eta)]
gens.append(((6,-1,-35,6),1))
gens += [(inv(g),mu) for g,mu in gens]
old={((1,0,0,1),1)};front=old
for _ in range(3):
 nxt={(mul(g,h),mu*nu) for g,mu in front for h,nu in gens}-old
 old|=nxt;front=nxt
R=[]
def add(rr,label,support=None):
 rr={j:K(v) for j,v in rr.items() if v}
 if rr and set(rr)<=U and (support is None or set(support)<=U):R.append((rr,label))
for (A,B,C,D),mu in sorted(old):
 for j in U:
  den=C*j+D*Q
  if not den:add({j:1},('ginf',A,B,C,D,j));continue
  if Q*(A*j+B*Q)%den:continue
  v=Q*(A*j+B*Q)//den%Q;c=mu*mon(Fraction(den*den,(A*D-B*C)*Q*Q))
  rr={j:K.one};rr[v]=rr.get(v,K.zero)-c;add(rr,('g',A,B,C,D,mu,j),[j,v])
for q in divisors(Q):
 ell=lcm(N,q*q)
 if Q*Q%ell:continue
 off=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
 add({j:1 for j in off},('R',q))
 d=Q*Q//ell
 for t0 in divisors(d):
  for t in [t0,-t0]:
   u=-d//t;c=-eta*(-bad5 if q%5==0 else 1)*(-bad7 if q%7==0 else 1)*mon(Fraction(ell*t*t,Q*Q))
   rr={};support=[]
   for j in off:
    j1=(j+t)%Q;j2=(j+u)%Q;support += [j1,j2]
    rr[j1]=rr.get(j1,K.zero)+1;rr[j2]=rr.get(j2,K.zero)+c
   add(rr,('F',q,t),support)
for p,ap in [(2,a),(3,b),(5,K(bad5)),(7,K(bad7))]:
 for j in range(Q//p):
  rr={j+t*(Q//p):K.one for t in range(p)}
  for col,val in [(p*j%Q,-ap/V[p]),(p*p*j%Q,K.zero if p in [5,7] else V[p]**-2)]:rr[col]=rr.get(col,K.zero)+val
  add(rr,('H',p,j))
def audit(poly):
 groups={}
 for powers,coef in poly.terms():groups.setdefault(powers[:4],[]).append(powers[4:])
 return any(len(t)==1 for t in groups.values())
def safe(v):return audit(v.numer) and audit(v.denom)
print('closed rows',len(R),flush=True);start=time.time();piv=[]
while R:
 choices=[i for i,(r,l) in enumerate(R) if any(safe(v) for v in r.values())]
 if not choices:break
 ii=min(choices,key=lambda i:len(R[i][0]));row,label=R.pop(ii)
 j=min((j for j,v in row.items() if safe(v)),key=lambda j:sum(j in rr for rr,ll in R))
 val=row[j];piv.append((j,str(val),label));row={c:v/val for c,v in row.items()};new=[]
 for rr,ll in R:
  if j in rr:
   v=rr[j]
   for c,u in row.items():
    rr[c]=rr.get(c,K.zero)-v*u
    if not rr[c]:del rr[c]
  if rr:new.append((rr,ll))
 R=new
 if len(piv)%10==0:print('pivots',len(piv),'remaining',len(R),'time',round(time.time()-start,1),flush=True)
 if time.time()-start>50:break
print('rank',len(piv),'target',len(U),'remaining',len(R),flush=True)
if len(piv)==len(U):
 print('FULL_GRID_UNIFORM_CONTINUATION_VERIFIED',eta,bad5,bad7,zero2,zero3,flush=True)
 Path('/tmp/level35_full_new_certificate.json').write_text(json.dumps({'eta':eta,'bad5':bad5,'bad7':bad7,'zero2':zero2,'zero3':zero3,'U':sorted(U),'pivots':piv}))

assert len(piv)==len(U), ('Incomplete closed subsystem',len(piv),len(U))

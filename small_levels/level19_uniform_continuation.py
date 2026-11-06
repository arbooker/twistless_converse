"""Exact symbolic leading-matrix certificate for all twists on the 1/114 grid.

Run with ETA BAD [zero2], where ETA=i^k epsilon_f and BAD=sqrt(19)*f_19
are independently +/-1. The optional zero2 specializes sqrt(2)*f_2=0;
omitting it verifies all nonzero sqrt(2)*f_2 simultaneously.
Example: PYTHONDONTWRITEBYTECODE=1 python3 level19_uniform_continuation.py -1 -1 zero2

Every pivot numerator/denominator is audited for an exponential monomial
coefficient that remains nonzero at every allowed specialization of a,b.
See the companion TeX fragment for why this proves meromorphic continuation,
and why it does not by itself cancel poles.
Runtime is less than one second per case on the development machine.
"""
import sys,time
def divisors(n):
 return [d for d in range(1,n+1) if n%d==0]
def canon(g):
 return tuple(-v for v in g) if next(v for v in g if v)<0 else g
def mul(g,h):
 a,b,c,d=g;e,f,q,r=h
 return canon((a*e+b*q,a*f+b*r,c*e+d*q,c*f+d*r))
def inv(g):
 a,b,c,d=g;return canon((d,-b,-c,a))
def known(N,depth):
 assert N==19
 gen=[(1,1,0,1),(1,0,19,1),(2,-1,-19,10)]
 gen+=list(map(inv,gen));old={(1,0,0,1)};front=old
 for _ in range(depth):
  nxt={mul(g,h) for g in front for h in gen}-old
  old|=nxt;front=nxt
 return old
from math import gcd,lcm
from fractions import Fraction
from sympy.polys.fields import field
from sympy import QQ
K,x,y,z,a,b=field('x,y,z,a,b',QQ)
N=19;Q=114
eta=int(sys.argv[1]) if len(sys.argv)>1 else -1
bad=int(sys.argv[2]) if len(sys.argv)>2 else -1
zero2=len(sys.argv)>3 and sys.argv[3]=='zero2'
if zero2:a=K.zero
V={2:x,3:y,19:z}
def mon(t):
 t=Fraction(t);num=abs(t.numerator);den=t.denominator;r=K.one
 for p,v in V.items():
  while num%p==0:num//=p;r*=v
  while den%p==0:den//=p;r/=v
 assert num==den==1,(t,num,den)
 return r
R=[]
def add(rr,label):
 rr={j:K(v) for j,v in rr.items() if v}
 if rr:R.append((rr,label))
for A,B,C,D in known(N,3):
 for j in range(Q):
  den=C*j+D*Q
  if not den:add({j:1},('ginf',A,B,C,D,j));continue
  num=A*j+B*Q
  if Q*num%den:continue
  v=Q*num//den%Q;c=mon(Fraction(den,Q))**2
  rr={j:K.one};rr[v]=rr.get(v,K.zero)-c;add(rr,('g',A,B,C,D,j))
for q in divisors(Q):
 ell=lcm(N,q*q)
 if Q*Q%ell:continue
 offsets=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
 add({j:1 for j in offsets},('R',q))
 d=Q*Q//ell
 for t0 in divisors(d):
  for t in [t0,-t0]:
   u=-d//t;c=mon(Fraction(ell*t*t,Q*Q))*(-eta)*(-bad if q%19==0 else 1)
   rr={}
   for j in offsets:
    j1=(j+t)%Q;j2=(j+u)%Q;rr[j1]=rr.get(j1,K.zero)+1;rr[j2]=rr.get(j2,K.zero)+c
   add(rr,('F',q,t))
for p,ap in [(2,a),(3,b),(19,K(bad))]:
 for j in range(Q//p):
  rr={j+t*(Q//p):K.one for t in range(p)}
  for col,val in [(p*j%Q,-ap/V[p]),(p*p*j%Q,K.zero if p==19 else V[p]**-2)]:rr[col]=rr.get(col,K.zero)+val
  add(rr,('H',p,j))
print('rows',len(R),flush=True)
def audit(poly):
 groups={}
 for powers,coef in poly.terms():
  key=powers[:3]
  groups.setdefault(key,[]).append((powers[3:],coef))
 return any(len(terms)==1 and terms[0][0][1]==0 and
            (not zero2 or terms[0][0][0]==0) for terms in groups.values())
piv=[];start=time.time()
while R:
 # Choose row with least terms; prefer simple coefficient when tied.
 ii=min(range(len(R)),key=lambda i:len(R[i][0]))
 row,label=R.pop(ii)
 j=min(row,key=lambda j: sum(j in rr for rr,ll in R))
 val=row[j];assert audit(val.numer),(len(piv),val,'numer');assert audit(val.denom),(len(piv),val,'denom');row={c:v/val for c,v in row.items()};piv.append((j,val,label))
 print(len(piv),'pivot',j,'len',len(row),'val',val,'remaining',len(R),'time',round(time.time()-start,1),flush=True)
 new=[]
 for rr,ll in R:
  if j in rr:
   v=rr[j]
   for c,u in row.items():
    rr[c]=rr.get(c,K.zero)-v*u
    if not rr[c]:del rr[c]
  if rr:new.append((rr,ll))
 R=new
 if time.time()-start>90:print('TIME LIMIT');break
assert len(piv)==Q and not R, 'The complete uniform continuation rank must be verified'
print('RANK',len(piv),'UNIFORM_AUDIT_PASSED',eta,bad,zero2,flush=True)

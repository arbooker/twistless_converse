"""N22 Q66 exact continuation test, with every known-map eigenvalue tracked.
Arguments ETA BAD2 BAD11 [zero3]. Without zero3, lambda3 is nonzero.
Every numerator/denominator pivot is audited for uniform specialization.
This is a continuation certificate, not a converse theorem.
"""
import sys,time
def divisors(n):
 return [d for d in range(1,n+1) if n%d==0]
from functools import reduce
from math import gcd
def canon(g):
 d=reduce(gcd,g);g=tuple(v//d for v in g)
 return tuple(-v for v in g) if next(v for v in g if v)<0 else g
def mul(g,h):
 a,b,c,d=g;e,f,q,r=h
 return canon((a*e+b*q,a*f+b*r,c*e+d*q,c*f+d*r))
def inv(g):
 a,b,c,d=g;return canon((d,-b,-c,a))
def known(N,depth):
 assert N==22
 gen=[((1,1,0,1),1),((1,0,22,1),1),((2,-1,-22,12),-bad2),((0,-1,22,0),eta)]
 gen+= [(inv(g),mu) for g,mu in gen]
 old={((1,0,0,1),1)};front=old
 for _ in range(depth):
  nxt={(mul(g,h),mu*nu) for g,mu in front for h,nu in gen}-old
  old|=nxt;front=nxt
 return old
from math import gcd,lcm
from fractions import Fraction
from sympy.polys.fields import field
from sympy import QQ
K,x,y,z,a,b=field('x,y,z,a,b',QQ)
N=22;Q=66
eta=int(sys.argv[1]) if len(sys.argv)>1 else -1
bad2=int(sys.argv[2]) if len(sys.argv)>2 else -1
bad11=int(sys.argv[3]) if len(sys.argv)>3 else -1
assert all(v in (-1,1) for v in [eta,bad2,bad11])
zero3='zero3' in sys.argv[4:]
if zero3:a=K.zero
V={2:x,3:y,11:z}
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
for (A,B,C,D),mu in known(N,3):
 for j in range(Q):
  den=C*j+D*Q
  if not den:add({j:1},('ginf',A,B,C,D,j));continue
  num=A*j+B*Q
  if Q*num%den:continue
  v=Q*num//den%Q;c=mu*mon(Fraction(den*den,(A*D-B*C)*Q*Q))
  rr={j:K.one};rr[v]=rr.get(v,K.zero)-c;add(rr,('g',A,B,C,D,mu,j))
for q in divisors(Q):
 ell=lcm(N,q*q)
 if Q*Q%ell:continue
 offsets=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
 add({j:1 for j in offsets},('R',q))
 d=Q*Q//ell
 for t0 in divisors(d):
  for t in [t0,-t0]:
   u=-d//t;c=mon(Fraction(ell*t*t,Q*Q))*(-eta)*(-bad2 if q%2==0 else 1)*(-bad11 if q%11==0 else 1)
   rr={}
   for j in offsets:
    j1=(j+t)%Q;j2=(j+u)%Q;rr[j1]=rr.get(j1,K.zero)+1;rr[j2]=rr.get(j2,K.zero)+c
   add(rr,('F',q,t))
for p,ap in [(2,K(bad2)),(3,a),(11,K(bad11))]:
 for j in range(Q//p):
  rr={j+t*(Q//p):K.one for t in range(p)}
  for col,val in [(p*j%Q,-ap/V[p]),(p*p*j%Q,K.zero if p!=3 else V[p]**-2)]:rr[col]=rr.get(col,K.zero)+val
  add(rr,('H',p,j))
print('rows',len(R),flush=True)
def audit(poly):
 groups={}
 for powers,coef in poly.terms():
  key=powers[:3]
  groups.setdefault(key,[]).append((powers[3:],coef))
 return any(len(terms)==1 and
            (not zero3 or terms[0][0][0]==0) and terms[0][0][1]==0 for terms in groups.values())
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
 if time.time()-start>45:print('TIME LIMIT');break
assert len(piv)==Q, ('incomplete rank',len(piv),Q)
print('RANK',len(piv),'UNIFORM_AUDIT_PASSED',eta,bad2,bad11,zero3,flush=True)

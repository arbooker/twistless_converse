"""N33 Q66 exact continuation test, with every known-map eigenvalue tracked.
Arguments ETA BAD3 BAD11 [zero2]. The symbolic parameter includes lambda2=0.
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
 assert N==33
 gen=[((1,1,0,1),1),((1,0,33,1),1),((2,-1,-33,17),1),((0,-1,33,0),eta)]
 gen.append(((6,-1,-33,6),-bad3))
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
N=33;Q=66
eta=int(sys.argv[1]) if len(sys.argv)>1 else -1
bad3=int(sys.argv[2]) if len(sys.argv)>2 else -1
bad11=int(sys.argv[3]) if len(sys.argv)>3 else -1
assert all(v in (-1,1) for v in [eta,bad3,bad11])
zero2='zero2' in sys.argv[4:]
if zero2:a=K.zero
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
   u=-d//t;c=mon(Fraction(ell*t*t,Q*Q))*(-eta)*(-bad3 if q%3==0 else 1)*(-bad11 if q%11==0 else 1)
   rr={}
   for j in offsets:
    j1=(j+t)%Q;j2=(j+u)%Q;rr[j1]=rr.get(j1,K.zero)+1;rr[j2]=rr.get(j2,K.zero)+c
   add(rr,('F',q,t))
for p,ap in [(2,a),(3,K(bad3)),(11,K(bad11))]:
 for j in range(Q//p):
  rr={j+t*(Q//p):K.one for t in range(p)}
  for col,val in [(p*j%Q,-ap/V[p]),(p*p*j%Q,K.zero if p!=2 else V[p]**-2)]:rr[col]=rr.get(col,K.zero)+val
  add(rr,('H',p,j))

print("rows",len(R),flush=True)

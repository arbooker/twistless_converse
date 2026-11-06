"""Exact matrix, generation and cusp-sign certificate for level32 converse.
No floating-point arithmetic, sampled ranks or Groebner algorithms are used.
"""
from fractions import Fraction as F
from math import gcd
from collections import deque
import json

def mul(g,h):
 a,b,c,d=g;e,f,u,v=h
 return (a*e+b*u,a*f+b*v,c*e+d*u,c*f+d*v)
def det(g):a,b,c,d=g;return a*d-b*c
def inv(g):
 a,b,c,d=g;q=det(g)
 return tuple(F(v,q) for v in (d,-b,-c,a))
def norm(g):
 assert all(F(t).denominator==1 for t in g)
 g=tuple(int(t) for t in g)
 return tuple(-t for t in g) if next(t for t in g if t)<0 else g
def scale(g,q):return tuple(q*t for t in g)
I=(1,0,0,1);T=(1,1,0,1);S=(0,-1,1,0)
W=(0,-1,2,0);D4=(1,0,0,4);D2=(1,0,0,2)
A=(3,2,4,3);B=(3,1,8,3);U=(1,0,8,1)
def M(j):return (1,j,0,3)
Minf=(3,0,0,1)
R2=(1,2,0,1)
assert mul(R2,M(-2))==M(4)
assert mul(R2,M(2))==M(8)
assert mul(mul(inv(W),M(0)),W)==Minf
assert mul(mul(inv(W),Minf),W)==M(0)
assert mul(mul(inv(W),M(2)),W)==(3,0,-4,1)
assert mul(mul(inv(W),M(-2)),W)==(3,0,4,1)
assert mul(A,M(-2))==(3,0,4,1)
assert mul(inv(A),M(2))==(3,0,-4,1)
E=mul(mul(M(-2),inv(M(2))),A)
assert E==(F(-7,3),-2,4,3) and det(E)==1 and E[0]+E[3]==F(2,3)
assert mul(mul(inv(D4),(0,-1,32,0)),D4)==scale(W,4)
assert mul(mul(D4,A),inv(D4))==mul(mul(D2,B),inv(D2))

# Explicit Schreier generation of Gamma0(8), indexed by P^1(Z/8Z).
def coset(g):
 c,d=g[2]%8,g[3]%8
 assert gcd(gcd(c,d),8)==1
 return min(((u*c)%8,(u*d)%8) for u in (1,3,5,7))
reps=[I];classes={coset(I):0};edges={}
for i,r in enumerate(reps):
 for label,x in [('s',S),('t',T)]:
  rx=mul(r,x);cl=coset(rx)
  if cl not in classes:classes[cl]=len(reps);reps.append(rx)
  edges[i,label]=classes[cl]
assert len(reps)==12
schreier=[]
for (i,label),j in edges.items():
 x=S if label=='s' else T
 gamma=norm(mul(mul(reps[i],x),inv(reps[j])))
 assert gamma[2]%8==0 and det(gamma)==1
 schreier.append((i,label,j,gamma))
targets={gamma for _,_,_,gamma in schreier}
generators={'t':T,'u':U,'b':B}
generators.update({s.upper():norm(inv(g)) for s,g in list(generators.items())})
words={I:''};front=deque([I]);remaining=targets-{I}
while front and remaining:
 g=front.popleft();word=words[g]
 assert len(words)<200000,'Bounded word search exceeded its certificate limit'
 for name,h in generators.items():
  gh=norm(mul(g,h))
  if gh in words:continue
  words[gh]=word+name;front.append(gh);remaining.discard(gh)
assert not remaining,remaining
for i,label,j,gamma in schreier:
 m=I
 for letter in words[gamma]:m=norm(mul(m,generators[letter]))
 assert m==gamma
print('SCHREIER_WORDS',json.dumps([{'from':i,'edge':label,'to':j,'matrix':g,'word':words[g]} for i,label,j,g in schreier]),flush=True)

# xi(gamma)=(-1)^(b+c/8). Its multiplicativity follows because a,d are odd.
def xi(g):
 a,b,c,d=g;assert det(g)==1 and c%8==0 and a%2 and d%2
 return -1 if (b+c//8)%2 else 1
assert [xi(T),xi(U),xi(B)]==[-1,-1,1]
# Four complete cusp classes of Gamma0(8); matrices sigma map infinity there.
cusps=[('infinity',I,1),('zero',S,8),('half',(1,0,2,1),2),('quarter',(1,0,4,1),1)]
for name,sigma,width in cusps:
 P=mul(mul(sigma,(1,width,0,1)),inv(sigma));P=tuple(int(v) for v in P)
 assert xi(P)==-1
 print('CUSP',name,'WIDTH',width,'STABILIZER',P,'XI',xi(P),flush=True)
print('PASS_LEVEL32_EXACT_CERTIFICATE',flush=True)

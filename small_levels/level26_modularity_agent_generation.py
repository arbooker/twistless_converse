"""Conditional N26 generation: G3 fixes f and P4 has character delta.
This file does not prove those two missing transformation laws.
"""
from pathlib import Path
from itertools import product
from functools import reduce
from math import gcd
import sys
I=(1,0,0,1)
def norm(g):
 d=abs(reduce(gcd,g));g=tuple(x//d for x in g)
 return tuple(-x for x in g) if next(x for x in g if x)<0 else g
def mul(x,y):
 a,b,c,d=x;e,f,g,h=y;return norm((a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h))
def inv(g):a,b,c,d=g;return norm((d,-b,-c,a))
def det(g):a,b,c,d=g;return a*d-b*c
T=(1,1,0,1);E=(2,-1,-26,14);W=(0,-1,26,0)
G3=(3,-1,-26,9);P4=(4,-1,26,-6)
base=[T,E,W,G3,P4];chars=[(0,0),(1,0),(0,1),(0,0),(1,0)]
reps={k:mul(E if k[0] else I,W if k[1] else I) for k in product(range(2),repeat=2)}
gens=set()
for key,r in reps.items():
 for g,cl in zip(base,chars):
  nxt=tuple(a^b for a,b in zip(key,cl));m=mul(mul(r,g),inv(reps[nxt]))
  assert det(m)==1 and m[2]%26==0
  if m!=I:gens.add(m)
S=(0,-1,1,0)
def power(g,n):
 if n<0:g=inv(g);n=-n
 out=I
 while n:
  if n&1:out=mul(out,g)
  g=mul(g,g);n//=2
 return out
def word(m):
 a,b,c,d=m;parts=[];value=I
 while c:
  q=a//c;parts.extend(['T^('+str(q)+')','S']);value=mul(mul(value,power(T,q)),S)
  a,b,c,d=-c,-d,a-q*c,b-q*d
 assert a==d and a in (-1,1)
 parts.append('T^('+str(b//a)+')');value=mul(value,power(T,b//a));assert value==m
 return '*'.join(parts)
output=Path(sys.argv[1] if len(sys.argv)>1 else '/tmp/level26_modularity_agent_generation.m')
output.write_text('G<S,T>:=Group<S,T|S^2,(S*T)^3>;\nH:=sub<G|'+','.join(word(m) for m in sorted(gens))+'>;\ni:=Index(G,H:CosetLimit:=50000,TimeLimit:=10);assert i eq 42;print "PASS: conditional N26 scalar kernel index",i;quit;\n')
# Known endpoint transformation supplying the coupled odd functional equation.
assert mul(mul(E,T),W)==norm((13,-1,-156,13))
print('PASS:',len(gens),'integral kernel generators, exact PSL2Z words, and /12 endpoint')

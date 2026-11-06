"""Conditional N33 generation once individual modulus-three Fricke laws are established.
All determinant-square-class-zero Schreier generators fix f, regardless
of the signs eta, lambda3.
"""
from level30_group_ring import norm,mul,inv,det,I
from sympy.combinatorics.free_groups import free_group
from sympy.combinatorics.fp_groups import FpGroup,coset_enumeration_r
from itertools import product
F,S,T=free_group('S,T');PSL=FpGroup(F,[S**2,(S*T)**3])
def word(m):
 a,b,c,d=m;out=F.identity
 while c:
  q=a//c;out=out*T**q*S;a,b,c,d=-c,-d,a-q*c,b-q*d
 assert a==d and a in [-1,1]
 return out*T**(b//a)
A=norm((3,-1,-33,12));W=norm((0,-1,33,0))
# Independent determinant classes3,33.
reps={}
for key in product([0,1],repeat=2):
 r=I
 for bit,g in zip(key,[A,W]):
  if bit:r=mul(r,g)
 reps[key]=r
std=[((1,1,0,1),(0,0)),((2,-1,-33,17),(0,0)),(A,(1,0)),(W,(0,1)),((6,-1,-33,6),(1,0)),((3,1,33,12),(1,0))]
gens=set()
for key,r in reps.items():
 for g,cl in std:
  nxt=tuple(a^b for a,b in zip(key,cl));m=mul(mul(r,g),inv(reps[nxt]))
  assert det(m)==1 and m[2]%33==0,(key,cl,m,det(m))
  if m!=I:gens.add(m)
def evaluate_word(u):
 r=I
 for letter,power in u.array_form:
  g=norm((0,-1,1,0)) if str(letter)=='S' else (1,1,0,1)
  if power<0:g=inv(g)
  for _ in range(abs(power)):r=mul(r,g)
 return r
for g in gens:assert evaluate_word(word(g))==norm(g)
assert len(gens)>0
print('Schreier generators',len(gens),flush=True)
C=coset_enumeration_r(PSL,[word(m) for m in sorted(gens)],max_cosets=1000)
assert C.is_complete();C.compress();print('index',C.n,flush=True)
assert C.n==48
print('LEVEL33_CONDITIONAL_GENERATION_VERIFIED',flush=True)

from math import gcd
cusps=[]
for key,r in sorted(reps.items()):
 # The reduced denominator of r infinity, and its Γ0 cusp label.
 den=0 if r[2]==0 else abs(r[2])//gcd(abs(r[0]),abs(r[2]))
 cusps.append(gcd(den,33))
assert sorted(cusps)==[1,3,11,33]
print('All four squarefree cusp classes represented:',sorted(cusps),flush=True)

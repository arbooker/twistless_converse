"""Exact level30 group generation with the modulus-six and modulus-four elliptic invariances.
All determinant-square-class-zero Schreier generators fix f, regardless
of the signs eta, lambda2, lambda3.
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
A=norm((16,1,30,2));B=norm((6,1,30,6));W=norm((0,-1,30,0))
# Independent determinant classes2,6,30.
reps={}
for key in product([0,1],repeat=3):
 r=I
 for bit,g in zip(key,[A,B,W]):
  if bit:r=mul(r,g)
 reps[key]=r
std=[((1,1,0,1),(0,0,0)),(A,(1,0,0)),(B,(0,1,0)),(W,(0,0,1)),((4,-1,-30,8),(1,0,0))]
gens=set()
for key,r in reps.items():
 for g,cl in std:
  nxt=tuple(a^b for a,b in zip(key,cl));m=mul(mul(r,g),inv(reps[nxt]))
  assert det(m)==1 and m[2]%30==0,(key,cl,m,det(m))
  if m!=I:gens.add(m)
def evaluate_word(u):
 r=I
 for letter,power in u.array_form:
  g=norm((0,-1,1,0)) if str(letter)=='S' else (1,1,0,1)
  if power<0:g=inv(g)
  for _ in range(abs(power)):r=mul(r,g)
 return r
for g in gens:assert evaluate_word(word(g))==norm(g)
assert len(gens)==26
print('Schreier generators',len(gens),flush=True)
C=coset_enumeration_r(PSL,[word(m) for m in sorted(gens)],max_cosets=1000)
assert C.is_complete();C.compress();print('index',C.n,flush=True)
assert C.n==72
print('LEVEL30_COMPLETE_GENERATION_VERIFIED',flush=True)

from math import gcd
cusps=[]
for key,r in sorted(reps.items()):
 # The reduced denominator of r infinity, and its Γ0 cusp label.
 den=0 if r[2]==0 else abs(r[2])//gcd(abs(r[0]),abs(r[2]))
 cusps.append(gcd(den,30))
assert sorted(cusps)==[1,2,3,5,6,10,15,30]
print('All eight squarefree cusp classes represented:',sorted(cusps),flush=True)
C4=(4,-1,-30,8);C4m=(4,1,30,8)
left=mul(W,inv(B));right=mul(W,B)
assert mul(mul(left,inv(C4)),right)==norm(C4m)
M=mul(mul(inv(C4),right),(2,-1,0,2))
assert M==norm((10,-2,30,-5))
assert 2*(M[0]+M[3])**2==5*det(M)
print('Modulus-four double coset and infinite elliptic matrix verified.')
# Initial Fricke comparisons: rational translations represented projectively.
def chain(*matrices):
 r=I
 for m in matrices:r=mul(r,m)
 return r
assert chain(inv(W),(2,1,0,2),(0,-1,60,0),(2,-1,0,2))==inv(A)
assert chain(inv(W),(6,1,0,6),(0,-1,180,0),(6,-1,0,6))==inv(B)
assert chain(inv(W),(4,1,0,4),(0,-1,240,0),(4,-1,0,4))==norm(C4)
assert chain(inv(W),(4,-1,0,4),(0,-1,240,0),(4,1,0,4))==norm(C4m)
print('All initial modulus-two, -six, and -four Fricke comparisons verified.')

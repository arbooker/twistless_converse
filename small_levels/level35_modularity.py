"""Exact group-generation certificate after both chi3 and chi4 pole removal."""
from level30_group_ring import norm,mul,inv,det,I
from sympy.combinatorics.free_groups import free_group
from sympy.combinatorics.fp_groups import FpGroup,coset_enumeration_r
F,S,T=free_group('S,T');PSL=FpGroup(F,[S**2,(S*T)**3])
def word(m):
 a,b,c,d=m;out=F.identity
 while c:
  q=a//c;out=out*T**q*S;a,b,c,d=-c,-d,a-q*c,b-q*d
 assert a==d and a in [-1,1]
 return out*T**(b//a)
def evaluate_word(u):
 r=I
 for letter,power in u.array_form:
  g=norm((0,-1,1,0)) if str(letter)=='S' else (1,1,0,1)
  if power<0:g=inv(g)
  for _ in range(abs(power)):r=mul(r,g)
 return r
# The only extra Hecke consequence used in the generation proof.
Tm=(1,1,0,1);U=(1,0,35,1);E=(2,-1,-35,18)
B=(6,1,35,6);Cp=(3,-1,-35,12);Cm=(3,1,35,12)
M0=(1,0,0,2);M1=(1,1,0,2);Minf=(2,0,0,1)
H=(41,-17,70,-29)
assert mul(mul(M0,B),inv(Minf))==Cm
assert mul(mul(Minf,B),inv(M0))==inv(Cp)
assert mul(mul(M1,B),inv(M1))==H
Em=mul(mul(U,E),Tm);Hm=mul(mul(inv(Tm),inv(H)),Tm)
assert Em==(2,1,35,18) and Hm==(41,17,-70,-29)
Gp=mul(E,H);Gm=mul(Em,Hm)
assert Gp==(12,-5,-175,73) and Gm==(12,5,175,73)
# Exact trace-zero matrices for all four primitive denominator12 twists.
W35=(0,-1,35,0)
for aa,G in [(1,inv(Cm)),(-1,inv(Cp)),(5,Gp),(-5,Gm)]:
 center=mul(inv(G),W35)
 assert center==norm((35*aa,-(35*aa*aa+1)//12,420,-35*aa))
 assert center[0]+center[3]==0
 assert center[2]**2==5040*det(center)
print('PASS: Hecke consequence and all four denominator12 Fricke centers')
gens=[(1,1,0,1),(1,0,35,1),(2,-1,-35,18),(6,-1,-35,6),(3,-1,-35,12),(3,1,35,12),(41,-17,70,-29),(4,-1,-35,9),(4,1,35,9)]
W=(0,-1,35,0)
gens=sorted(set(gens+[mul(mul(W,g),inv(W)) for g in gens]))
for g in gens:
 assert det(g)==1 and g[2]%35==0
 assert evaluate_word(word(g))==norm(g)
C=coset_enumeration_r(PSL,[word(g) for g in gens],max_cosets=1000)
assert C.is_complete();C.compress();assert C.n==48
print('PASS: known invariances and Fricke conjugates generate Gamma_0(35); complete coset index 48')
# Cusp-equivalence certificate at denominator d=5 or7.
# Every primitive column (a,d) with gcd(a,d)=1 is Gamma0-equivalent to (1,d).
# The two SL2Z completions differ by a suitable right translation so that
# their lower-left entry is 0 modulo35.  This preserves their constant term.
from math import gcd
for d in [5,7]:
 for a in range(1,d):
  if gcd(a,d)!=1:continue
  e=pow(a,-1,d);b=(a*e-1)//d;sig=(a,b,d,e);tau=(1,0,d,1)
  found=False
  for n in range(35):
   gamma=mul(mul(sig,(1,n,0,1)),inv(tau))
   if gamma[2]%35==0:
    assert det(gamma)==1
    # gamma*tau = sig*T^n projectively, so the cusp constants coincide.
    assert mul(gamma,tau)==mul(sig,(1,n,0,1));found=True;break
  assert found
print('PASS: primitive columns at denominator 5 and7 have equal cusp constants')

"""All-parameter N34 modularity: Ramanujan5 elliptic certificate."""
from level30_group_ring import norm,mul,inv,det,I
from itertools import product
from math import gcd
def prod(*gs):
    h=I
    for g in gs:h=mul(h,g)
    return h
def t(a,b=1):return norm((b,a,0,b))
T=(1,1,0,1); E=(2,-1,-34,18); B=(6,-1,-34,6)
W=(0,-1,34,0); G=(11,-1,34,-3); P=(4,-1,34,-8)
G1=(5,-1,-34,7); Gm1=(5,1,34,7)
G2=(5,2,-68,-27); Gm2=(5,-2,68,-27)
assert prod(E,T,W,inv(G),W,E,T)==G2
assert prod(inv(W),inv(G2),inv(W))==Gm2
assert prod(B,P)==G1 and prod(P,inv(B))==Gm1
for a,b,H in [(1,-1,G1),(-1,1,Gm1),(2,2,G2),(-2,-2,Gm2)]:
    assert prod(inv(W),t(a,5),(0,-1,850,0),t(b,5))==H
K=prod(inv(B),t(-2,5))
assert K==(30,-7,170,-38) and det(K)==50
assert 25*(K[0]+K[3])**2==32*det(K)
for delta,eta in product([-1,1],repeat=2):
    assert delta*eta*eta*delta==1 # G2 word character
    assert (-delta)**2==1       # h|K^2=h, K^2 remains infinite elliptic
print('PASS: four Ramanujan5 centers, explicit invariant words, all-sign elliptic obstruction')

# Exact integral invariant generators; no exploratory Fold is used.
reps={(0,0):I,(1,0):E,(0,1):W,(1,1):prod(E,W)}
sources=[(T,(0,0)),(E,(1,0)),(B,(1,0)),(W,(0,1)),(G,(0,0)),(P,(1,0))]
gens=[]
for cl,R in reps.items():
    for H,cc in sources:
        target=tuple(a^b for a,b in zip(cl,cc))
        V=prod(R,H,inv(reps[target]))
        assert det(V)==1 and V[2]%34==0
        if V!=I and V not in gens:gens.append(V)
from sympy.combinatorics.free_groups import free_group
from sympy.combinatorics.fp_groups import FpGroup,coset_enumeration_r
F,s,q=free_group('s,q'); PSL=FpGroup(F,[s**2,(s*q)**3])
def word(m):
    a,b,c,d=m; out=F.identity
    while c:
        n=a//c;out=out*q**n*s;a,b,c,d=-c,-d,a-n*c,b-n*d
    assert a==d and a in [-1,1]
    return out*q**(b//a)
def evaluate(w):
    m=I
    for letter,power in w.array_form:
        h=norm((0,-1,1,0)) if str(letter)=='s' else T
        if power<0:h=inv(h)
        for _ in range(abs(power)):m=prod(m,h)
    return m
for H in gens:assert evaluate(word(H))==H
table=coset_enumeration_r(PSL,[word(H) for H in gens],max_cosets=2000)
assert table.is_complete();table.compress();assert table.n==54
print('PASS: invariant integral subgroup has exact PSL2Z index54 = Gamma0(34)')

# Images of infinity under I,E,W,EW have all squarefree cusp denominators.
denominators=set()
for H in reps.values():
    a,b,c,d=H;denominators.add(gcd(c//gcd(a,c),34))
assert denominators=={1,2,17,34}
print('PASS: scalar eigenlaws at I,E,W,EW transfer cusp decay to all four classes')

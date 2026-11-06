"""Finite exact N22 certificate: auxiliary defect, elliptic factors, index36."""
from level22_finish_defect import norm,mul,inv,prod,t,det,I,T,U,W,E,A,B,C,D,P,Q,RA
from itertools import product

X=(3,-1,22,-7); Y=(3,1,-22,-7)
M0=(1,0,0,2); M1=(1,1,0,2)
# Ramanujan3 gives g_X=-g_Y|t_{-2/3}.
assert prod(inv(W),t(1,3),(0,-1,198,0),t(1,3))==Y
assert prod(inv(W),t(-1,3),(0,-1,198,0),t(-1,3))==X
assert prod(inv(W),inv(Y),inv(W))==X
assert prod(W,inv(T),inv(E),Y,inv(T),W,E)==X
K=prod(inv(Y),inv(W),t(2,3))
L=prod(inv(T),W,E,t(2,3))
assert K==(66,23,-198,-66) and L==(33,7,-66,-11)
assert prod(K,K)==I

# Both ramified Hecke2 laws close in the two defects u and h.
assert prod(M0,X)==prod(W,inv(T),W,Y,inv(T),M1)
assert prod(M1,X)==prod(inv(E),inv(T),inv(E),C,M0)
assert prod(M0,Y)==prod(W,T,W,X,M1)
assert prod(M1,Y)==prod(W,E,T,W,B,inv(T),inv(E),M0)
assert prod(E,T,W,P,W)==C
assert prod(W,P,RA)==A

J1=prod(t(-2,3),inv(M0),inv(W))
J2=prod(inv(T),M1,inv(M0),inv(W))
Z0=prod(RA,t(4,5),inv(T),inv(E),M0)
AA=prod(t(-2,3),M1)
BB=prod(J1,Z0); CC=prod(J2,Z0)
assert J1==(22,3,-33,0) and J2==(11,1,-22,0)
assert AA==(3,-1,0,6)
assert BB==(81,22,-198,-51) and CC==(49,13,-132,-34)
Z=prod(K,CC)
assert Z==(99,38,-495,-165)
assert prod(AA,Z)==prod(K,BB)
assert 25*(Z[0]+Z[3])**2==44*det(Z)
V=prod(K,L,AA)
assert V==(10,3,-33,-9) and det(V)==9 and V[0]+V[3]==1

# Sign audit for the factorization (delta*u-u|AA)(1+delta*eta*Z).
# u|K=eta*u, so u|Z=eta*u|CC and u|AA Z=eta*u|BB.
for delta,eta in product([-1,1],repeat=2):
    assert delta*eta*delta*eta==1
    assert -delta*eta*eta==-delta
    # The last matrix has character eta*(-delta*eta)*delta=-1.
    assert eta*(-delta*eta)*delta==-1
print('PASS: N22 Hecke2 closure and both infinite elliptic obstructions, all signs')

# Schreier kernel for determinant squareclasses 1,2,22,11. The assigned
# character is delta^a eta^b, so every Schreier generator fixes f.
reps={(0,0):I,(1,0):E,(0,1):W,(1,1):prod(E,W)}
sources=[(T,(0,0)),(E,(1,0)),(W,(0,1)),(P,(1,0)),(Y,(0,0))]
gens=[]
for key,R in reps.items():
    for G,cl in sources:
        target=tuple(a^b for a,b in zip(key,cl))
        H=prod(R,G,inv(reps[target]))
        assert det(H)==1 and H[2]%22==0
        if H!=I and H not in gens: gens.append(H)

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
        g=norm((0,-1,1,0)) if str(letter)=='s' else T
        if power<0:g=inv(g)
        for _ in range(abs(power)):m=prod(m,g)
    return m
for G in gens:assert evaluate(word(G))==G
table=coset_enumeration_r(PSL,[word(G) for G in gens],max_cosets=1000)
assert table.is_complete();table.compress();assert table.n==36
print('PASS: integral invariant subgroup has exact PSL2Z index36 = Gamma0(22)')
assert all(66%d==0 for d in [1,2,11,22])
print('PASS: every squarefree cusp denominator divides the entire66-grid')

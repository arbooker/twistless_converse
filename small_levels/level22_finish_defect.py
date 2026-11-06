"""Exact checks for the open N=22 modularity reduction. No completeness claim."""
from functools import reduce
from math import gcd
from itertools import product

def norm(g):
    d = reduce(gcd, g)
    g = tuple(a // d for a in g)
    return tuple(-a for a in g) if next(a for a in g if a) < 0 else g

def mul(g, h):
    a,b,c,d=g; e,f,j,l=h
    return norm((a*e+b*j,a*f+b*l,c*e+d*j,c*f+d*l))

def inv(g):
    a,b,c,d=g
    return norm((d,-b,-c,a))

def prod(*gs):
    h=(1,0,0,1)
    for g in gs: h=mul(h,g)
    return h

def t(a,b=1): return norm((b,a,0,b))
def det(g): return g[0]*g[3]-g[1]*g[2]

I=(1,0,0,1); T=t(1); U=(1,0,22,1)
W=(0,-1,22,0); E=(2,-1,-22,12)
A=(5,-2,-22,9); B=(5,2,22,9)
C=(5,-1,-44,9); D=(5,1,44,9)
P=(4,1,22,6); Q=(4,-1,-22,6)
RA=prod(inv(T),W,E); RB=prod(W,E,T)
RC=prod(inv(E),inv(U)); RD=prod(inv(T),inv(E))

# The exchanged even denominator-five laws have these exact matrix factors.
for a,b,G in [(1,-2,A),(-1,2,B),(2,-1,C),(-2,1,D)]:
    assert prod(inv(W),t(a,5),(0,-1,550,0),t(b,5)) == G
assert prod(W,P,RA)==A
assert prod(W,Q,RB)==B
assert prod(E,T,A,RC)==C
assert prod(U,E,B,RD)==D
assert prod(inv(W),inv(A),inv(W))==C
assert prod(inv(W),inv(B),inv(W))==D

KA=prod(inv(A),inv(W),inv(RC))
KB=prod(t(4,5),inv(B),inv(W),inv(RD),t(-4,5))
K1=prod(RA,KA,inv(RA)); K2=prod(RA,KB,inv(RA))
assert K1==(11,3,-44,-11)
assert K2==(649,207,-2068,-649)
assert prod(K1,K1)==I and prod(K2,K2)==I
S=prod(RA,t(4,5),inv(RB))

Ms=[(1,j,0,3) for j in range(3)]+[(3,0,0,1)]
Pfactors=[(prod(W,inv(T)),B,RA,1),(W,C,prod(W,E),2),
          (inv(E),C,T,3)]
Qfactors=[(prod(W,T),A,prod(W,E),2),
          (I,B,prod(inv(T),inv(E),inv(T)),3),
          (prod(T,W),D,RA,1)]
for i,(L,G,R,j) in enumerate(Pfactors):
    assert prod(Ms[i],P)==prod(L,G,R,Ms[j])
for i,(L,G,R,j) in enumerate(Qfactors):
    assert prod(Ms[i],Q)==prod(L,G,R,Ms[j])
assert prod(Ms[3],P)==prod(inv(E),Ms[0])
assert prod(Ms[3],Q)==prod(inv(T),W,E,T,W,Ms[0])

# Reduce the two three-term Hecke equations using the single explicit
# stabilizer K2*K1, whose character is 1 for all signs.
V=[(17,-1,-44,7),(0,1,-66,-22),(27,11,-132,-51),
   (1672,421,-4554,-1122)]
for delta,eta in product([-1,1],repeat=2):
    defects={A:(eta,RA),B:(-eta,prod(RA,t(4,5))),
             C:(delta*eta,W),D:(-delta*eta,prod(RA,t(4,5),RD))}
    pterms=[]; qterms=[]
    for outer,G,R,j in [(eta,B,RA,1),(eta,C,prod(W,E),2),(delta,C,T,3)]:
        coefficient,M=defects[G]
        pterms.append((outer*coefficient,prod(M,R,Ms[j])))
    for outer,G,R,j in [(eta,A,prod(W,E),2),
                        (1,B,prod(inv(T),inv(E),inv(T)),3),(eta,D,RA,1)]:
        coefficient,M=defects[G]
        qterms.append((outer*coefficient,prod(M,R,Ms[j],inv(S))))
    assert pterms[1][0]+qterms[2][0]==0
    assert prod(qterms[2][1],inv(pterms[1][1]))==prod(K2,K1)
    assert [pterms[0],pterms[2],qterms[0],qterms[1]]==list(zip([-1,eta,1,-eta],V))

print("PASS: N22 paired laws, both involutions, all Hecke3 factors, four-term identity in all four signs")

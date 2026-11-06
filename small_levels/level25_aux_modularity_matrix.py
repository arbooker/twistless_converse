"""N25 exact modularity algebra. Analytic pole-control input remains separate."""
from level30_group_ring import norm,mul,inv,det,I
def prod(*gs):
    h=I
    for g in gs:h=mul(h,g)
    return h
def t(a,b=1):return norm((b,a,0,b))
T=(1,1,0,1);U=(1,0,25,1);E=(2,-1,-25,13);W=(0,-1,25,0)
A=(3,1,-25,-8);Ap=(3,-1,25,-8)
B=(4,1,-25,-6);Bp=(4,-1,25,-6)
C=inv(B);Cp=inv(Bp)
assert prod(W,inv(T),inv(W))==U
for q,G,Gp in [(3,A,Ap),(4,B,Bp),(6,C,Cp)]:
    assert prod(inv(W),t(1,q),(0,-1,25*q*q,0),t(1,q))==G
    assert prod(inv(W),t(-1,q),(0,-1,25*q*q,0),t(-1,q))==Gp
    assert prod(inv(W),inv(G),inv(W))==Gp
Ku=prod(inv(A),inv(W),t(2,3))
assert Ku==(75,26,-225,-75) and prod(Ku,Ku)==I
# With v=f|B-f, the q4/q6 pair equations imply v|M=v.
Lv=prod(t(-1,2),inv(Bp),t(1,3),B)
M=inv(Lv)
assert M==(6,3,-50,-19) and det(M)==36
assert 25*M[1]+5*(M[3]-M[0])-M[2]==0 # fixed point -1/5
assert 100*M[1]+30*(M[3]-M[0])-9*M[2]==0 # fixed point -3/10
assert B[0]+B[3]==-2 and det(B)==1
assert 25*B[1]+5*(B[3]-B[0])-B[2]==0

# Assuming B fixes f, the Hecke2 law for A closes solely on u=f|A-f.
Minf=(2,0,0,1);M0=(1,0,0,2);M1=(1,1,0,2)
H1=inv(U);H2=prod(inv(E),inv(U))
G1=(3,-1,-50,17);G2=(11,7,25,16)
assert H2==(12,-1,25,-2)
assert prod(Minf,A)==prod(inv(B),M0)
assert prod(M0,A)==prod(G1,M1)
assert prod(M1,A)==prod(G2,Minf)
assert prod(H1,W,inv(A),W)==G1
assert prod(H2,W,inv(A),W,T)==G2
D=prod(t(-2,3),M1)
assert D==(3,-1,0,6)
assert prod(t(1,3),Minf)==inv(D)
# u|Ku=eta*u => eta*u|A^-1 W=u|t(-2/3).
assert prod(inv(A),W)==prod(Ku,t(-2,3))
print('PASS: q3/q4/q6 pairs, rational hyperbolic fixed points, exact Hecke2 recurrence')

# Conditional on the analytic argument proving both A and B invariance.
gens=[T,U,E,A,B]
gens=list(dict.fromkeys(gens+[prod(W,G,inv(W)) for G in gens]))
assert all(det(G)==1 and G[2]%25==0 for G in gens)
from sympy.combinatorics.free_groups import free_group
from sympy.combinatorics.fp_groups import FpGroup,coset_enumeration_r
F,s,q=free_group('s,q'); PSL=FpGroup(F,[s**2,(s*q)**3])
def word(m):
    a,b,c,d=m;out=F.identity
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
for G in gens:assert evaluate(word(G))==G
table=coset_enumeration_r(PSL,[word(G) for G in gens],max_cosets=1000)
assert table.is_complete();table.compress();assert table.n==30
print('PASS: conditional invariant integral subgroup index30 = Gamma0(25)')

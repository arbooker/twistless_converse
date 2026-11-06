"""Exact matrix part of conditional N26 modularity.
Analytic hypothesis: D_{2/13},D_{+/-1/3} have only possible simple poles at k.
Analytic transport and dense-hyperbolic arguments are in the paired .tex.
"""
from fractions import Fraction as F
from level26_modularity_agent_generation import *
def t(a,b=1):return norm((b,a,0,b))
P=P4;Q=(4,1,-26,-6);P6=(6,-1,26,-4);Q6=(6,1,-26,-4)
assert norm(P6)==inv(P) and norm(Q6)==inv(Q)
for q,PP,QQ,C in [(4,P,Q,208),(6,P6,Q6,468)]:
 WC=(0,-1,C,0)
 assert mul(mul(inv(W),t(-1,q)),WC)==mul(PP,t(1,q))
 assert mul(mul(inv(W),t(1,q)),WC)==mul(QQ,t(-1,q))
assert norm(Q)==mul(mul(inv(W),inv(P)),inv(W))
M=mul(mul(mul(t(1,2),inv(Q)),t(-1,3)),P)
K=mul(mul(inv(P),inv(W)),t(-1,2));P2=mul(P,P)
assert M==(20,-3,52,-6) and det(M)==36 and M[0]+M[3]==14
assert K==(26,-7,104,-26) and mul(K,K)==I
assert P2==(5,-1,26,-5) and mul(P2,P2)==I
assert mul(mul(P2,M),inv(P2))==inv(M)
MP=mul(M,P)
assert F((MP[0]+MP[3])**2,det(MP))==F(49,18)
Z=mul(K,P2)
assert Z==(52,-9,156,-26) and det(Z)==52 and Z[0]+Z[3]==26
assert mul(M,Z)==mul(Z,M)
# Fixed points of M and Z are roots of 52r^2-26r+3.
assert (M[2],M[3]-M[0],-M[1])==(52,-26,3)
assert (Z[2],Z[3]-Z[0],-Z[1])==(156,-78,9)
assert F(P[0],P[2])==F(2,13)
# Q(sqrt13) exact arithmetic checks the expanding eigenvalues.
def qm(a,b):return (a[0]*b[0]+13*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def qa(a,b):return (a[0]+b[0],a[1]+b[1])
a=(F(7,6),F(1,6));b=(F(3,2),F(1,2))
assert qa(qa(qm(a,a),(-F(7,3)*a[0],-F(7,3)*a[1])),(1,0))==(0,0)
assert qa(qa(qm(b,b),(-3*b[0],-3*b[1])),(-1,0))==(0,0)
assert F(7,3).denominator!=1
print('PASS: Ramanujan4/6 pairing, defect M/K, P order4, elliptic49/18')
print('PASS: commuting hyperbolics, common fixed points, nonintegral/unit eigenvalues')
print('PASS: required transport cusp is exactly 2/13')

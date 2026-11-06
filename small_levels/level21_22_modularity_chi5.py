"""Exact all-parameter chi_5 algebra and level-21 transformations.

Analytic inputs: entireness of the original 42/66 grids, proved in the
weight2 closure notes together with the earlier all-sign pole theorems.
This verifies the algebra used in the companion proof; it does not assert
full modularity or use a numerical eigenvalue specialization.
"""
import sympy as s
x, a, R, B = s.symbols('x a R B', nonzero=True)
t=lambda r:s.Matrix([[1,s.Rational(r)],[0,1]])
w=lambda n:s.Matrix([[0,-1],[n,0]])
for n in [21,22]:
    E=s.Matrix([[2,-1],[-n,11 if n==21 else 12]])
    ell=2100 if n==21 else 1100
    scalar=-s.Rational(1,10 if n==21 else 5)
    assert E*t(1)*w(n)==scalar*t(-s.Rational(1,10))*w(ell)*t(-s.Rational(1,10))
C=x+1/x
q21=((C-a)*R+2*x*B)/(C+a)
# After applying the expected conductor-525 reflection, R is fixed,
# x becomes 1/x and B acquires the conductor ratio 4^h=x^2.
assert s.cancel(q21-q21.subs({x:1/x,B:x*x*B}, simultaneous=True))==0
for sigma in [-1,1]:
    q22=((x-sigma)*R+2*x*B)/(x+sigma)
    # The expected chi5 sign is minus; the even tenth-sum sign is -sigma.
    reflected=-q22.subs({x:1/x,B:-sigma*x*B}, simultaneous=True)
    assert s.cancel(q22-reflected)==0
A=s.Matrix([[5,1],[-21,-4]])
BB=s.Matrix([[5,-1],[21,-4]])
Cmat=s.Matrix([[5,-2],[-42,17]])
D=s.Matrix([[5,2],[42,17]])
E=s.Matrix([[2,-1],[-21,11]])
U=s.Matrix([[1,0],[21,1]])
assert all(g.det()==1 for g in [A,BB,Cmat,D,E,U])
assert Cmat==E*t(1)*D.inv()*U*E
assert D==U*E*Cmat.inv()*E*t(1)
M=Cmat.inv()*E*t(s.Rational(1,5))
assert M==s.Matrix([[-8,s.Rational(17,5)],[-21,s.Rational(44,5)]])
assert M.det()==1 and s.trace(M)==s.Rational(4,5)
M0=s.Matrix([[2,0],[0,1]])
M1=s.Matrix([[1,0],[0,2]])
M2=s.Matrix([[1,1],[0,2]])
assert M0*A==-t(-1)*E.inv()*M1
assert M1*A==Cmat*M2
assert M2*A==E.inv()*U.inv()*D*M0
print('PASS: all-parameter chi5 functional-equation algebra for levels 21 and 22')
print('PASS: level21 C,D invariance; lambda2*(f|A-f)=0; elliptic trace 4/5')

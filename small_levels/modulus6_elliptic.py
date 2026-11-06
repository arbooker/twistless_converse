"""Exact matrix checks for the modulus-six elliptic law at30,33,34,35."""
from sympy import Matrix,Rational
from math import gcd,lcm
def t(r):return Matrix([[1,r],[0,1]])
def W(n):return Matrix([[0,-1],[n,0]])
for N in [30,33,34,35]:
 d=36-N;ell=lcm(N,36)
 assert gcd(N,36)==d and ell==N*36//d
 G=Matrix([[6,-1],[-N,6]])
 Gm=Matrix([[6,1],[N,6]])
 assert G.det()==d and Gm==d*G.inv()
 for a in [-1,1]:
  assert Rational(d,6)*W(N).inv()*t(Rational(a,6))*W(ell)*t(Rational(-a,6))==Matrix([[6,-a],[-N*a,6]])
 M=Gm*t(Rational(-1,3))
 ratio=M.trace()**2/M.det()
 assert ratio==Rational(d,9) and 0<ratio<4 and ratio.q!=1
 # Centers corresponding to the eigenlaw for G^{-1}.
 assert Gm*W(N)==Rational(d,6)*t(Rational(1,6))*W(ell)*t(Rational(-1,6))
 print(N,'ell',ell,'elliptic trace-square ratio',ratio,'PASS')

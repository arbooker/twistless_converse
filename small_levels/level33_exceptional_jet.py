"""Exact higher-Taylor check at the sole surviving first-jet candidate.
The candidate is eta=bad11=-1, bad3=+1, h=1, lambda2=-5/2.
"""
import sys
from pathlib import Path
sys.argv=[sys.argv[0],'-1','1','-1']
src=Path(__file__).with_name('level33_first_jet.py').read_text()
exec(src[:src.index('from sympy import symbols,Poly,groebner')])
from sympy import symbols,Rational,factor,factorial
point=dict(zip(symbols('x y z a b'),[2,3,11,Rational(-5,2),0]))
def ev(v,n=0):return shift(v,n).as_expr().subs(point)
from sympy import Matrix
M=Matrix([[ev(v) for v in row] for row in lead])
ns=M.nullspace();assert len(ns)==1
c=ns[0]
prev=[[sum(ev(kernels[i][j])*c[i] for i in range(2)) for j in range(Q)]]
assert any(prev[0])
assert all(sum(ev(c)*prev[0][j] for j,c in row.items())==0 for row,lab in original)
def source(lab,n):
 if lab[0]=='g':
  _,A,B,C,D,mu,j=lab;den=C*j+D*Q;dest=Q*(A*j+B*Q)//den%Q;det=A*D-B*C
  leading=mu*mon(Fraction(den*den,det*Q*Q));slope=Rational(C*den,det*Q)
  return ev(leading,n)*sum(slope**m/factorial(m)*prev[n-m][dest] for m in range(1,n+1))
 if lab[0]=='F':
  _,q,t=lab;ell=lcm(N,q*q);d=Q*Q//ell;dest=-d//t
  eta_q=eta*(-bad3 if q%3==0 else 1)*(-bad11 if q%11==0 else 1)
  leading=eta_q*mon(Fraction(ell*t*t,Q*Q));slope=Rational(ell*t,Q)
  off=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
  return ev(leading,n)*sum(slope**m/factorial(m)*sum(prev[n-m][(j+dest)%Q] for j in off) for m in range(1,n+1))
 return Rational(0)
for n in range(1,5):
 basis={};bad=[]
 for row,lab in original:
  r={j:ev(v,n) for j,v in row.items()};r={j:v for j,v in r.items() if v};b=source(lab,n)
  while r:
   j=min(r)
   if j not in basis:
    val=r[j];basis[j]=({i:v/val for i,v in r.items()},b/val);break
   base,bb=basis[j];val=r[j];b-=val*bb
   for i,v in base.items():
    r[i]=r.get(i,Rational(0))-val*v
    if not r[i]:del r[i]
  else:
   if b:bad.append((lab,b))
 print('order',n,'rank',len(basis),'obstructions',bad[:4],flush=True)
 if bad:
  assert n==3
  assert len(basis)==Q
  assert any(lab==('H',2,24) and value==300806 for lab,value in bad)
  print('N33_EXCEPTIONAL_JET_VERIFIED',flush=True)
  break
 assert len(basis)==Q
 w=[Rational(0)]*Q
 for j in sorted(basis,reverse=True):
  row,b=basis[j];w[j]=b-sum(v*w[i] for i,v in row.items() if i!=j)
 prev.append(w)
else:raise AssertionError('No obstruction found by order four')

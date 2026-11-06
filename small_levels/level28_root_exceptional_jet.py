"""Exact shifted Taylor probe in the Q84 constant-kernel quotient."""
import sys
from pathlib import Path
sys.argv=[sys.argv[0],'-1','-1']
base=Path(__file__).parent
src=(base/'level28_root_constraints.py').read_text()
exec(src[:src.index('import sympy as sp')])
from sympy import symbols,Rational,factorial
point=dict(zip(symbols('x y z a b'),[2,3,7,Rational(-10,3),0]))
def ev(v,n=0):return shift(v,n).as_expr().subs(point)
assert free==[24,53]
prev=[[ev(v) for v in kernels[0]]]
assert all(sum(ev(c)*prev[0][j] for j,c in row.items())==0 for row,lab in original)
original.append(({53:K.one},('gauge',)))
def source(lab,n):
 if lab[0]=='g':
  _,A,B,C,D,mu,j=lab;den=C*j+D*Q;dest=Q*(A*j+B*Q)//den%Q;det=A*D-B*C
  leading=mu*mon(Fraction(den*den,det*Q*Q));slope=Rational(C*den,det*Q)
  return ev(leading,n)*sum(slope**m/factorial(m)*prev[n-m][dest] for m in range(1,n+1))
 if lab[0]=='F':
  _,q,t=lab;ell=lcm(N,q*q);dest=-(Q*Q//ell)//t
  leading=eta*(-bad7 if q%7==0 else 1)*mon(Fraction(ell*t*t,Q*Q));slope=Rational(ell*t,Q)
  off=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
  return ev(leading,n)*sum(slope**m/factorial(m)*sum(prev[n-m][(j+dest)%Q] for j in off) for m in range(1,n+1))
 return Rational(0)
for n in range(1,6):
 basis={};bad=[]
 for row,lab in original:
  r={j:ev(v,n) for j,v in row.items()};r={j:v for j,v in r.items() if v};b=source(lab,n)
  while r:
   j=min(r)
   if j not in basis:
    val=r[j];basis[j]=({i:v/val for i,v in r.items()},b/val);break
   row0,b0=basis[j];val=r[j];b-=val*b0
   for i,v in row0.items():
    r[i]=r.get(i,Rational(0))-val*v
    if not r[i]:del r[i]
  else:
   if b:bad.append((lab,b))
 print('order',n,'rank',len(basis),'obstructions',bad[:4],flush=True)
 if bad:
  assert n==3 and len(basis)==Q
  assert any(lab==('R',7) and value==Rational(68600,81) for lab,value in bad)
  print('N28_EXCEPTIONAL_QUOTIENT_THIRD_JET_VERIFIED',flush=True)
  break
 assert len(basis)==Q
 w=[Rational(0)]*Q
 for j in sorted(basis,reverse=True):
  row,b=basis[j];w[j]=b-sum(v*w[i] for i,v in row.items() if i!=j)
 prev.append(w)
else: raise AssertionError('Expected third-order obstruction missing')

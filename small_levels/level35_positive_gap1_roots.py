"""Exact rational Rouche disks and physical-modulus exclusion; no numerical oracle."""
import sympy as s,json
from fractions import Fraction as F
from math import isqrt,comb
from pathlib import Path
D=json.loads(Path(__file__).with_name('level35_positive_gap1_disks.json').read_text())
X=s.Symbol('u');p=s.Poly(s.sympify(D['p']),X);fy=s.Poly(X**2-s.Rational(5,2)*X-2,X)
def coeffs(p):return [F(p.nth(i)) for i in range(p.degree()+1)]
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def scale(a,b):return (a[0]*b,a[1]*b)
def pw(a,n):
 r=(F(1),F(0))
 for _ in range(n):r=mul(r,a)
 return r
def sqrtbound(q):
 S=10**40;k=isqrt(q.numerator*S*S//q.denominator);return F(k,S),F(k+1,S)
def norm(a):return sqrtbound(a[0]**2+a[1]**2)
def tay(cs,c):return [sumc([scale(pw(c,n-j),v*comb(n,j)) for n,v in enumerate(cs) if n>=j]) for j in range(len(cs))]
def sumc(vs):
 r=(F(0),F(0))
 for v in vs:r=add(r,v)
 return r
centers=[];outer=0
for disk in D['disks']:
 c=tuple(F(q) for q in disk['center']);r=F(disk['radius']);centers.append(c)
 ts=tay(coeffs(p),c);rest=norm(ts[0])[1]+sum(norm(ts[j])[1]*r**j for j in range(2,len(ts)))
 assert norm(ts[1])[0]*r>rest
 lo,hi=norm(c);lo-=r;hi+=r
 if hi<4:continue
 outer+=1
 assert lo>4 and hi<8
 ys=tay(coeffs(fy),c);err=sum(norm(ys[j])[1]*r**j for j in range(1,len(ys)))
 assert norm(ys[0])[0]-err>27
for i,c in enumerate(centers):
 for d in centers[i+1:]:assert norm((c[0]-d[0],c[1]-d[1]))[0]>2*r
assert len(centers)==p.degree()==7 and outer==1
print('PASS: seven exact disjoint Rouche disks; sole |u|>=4 root has |Y|>27 and |u|<8')

"""Exact rational Rouche disks and physical-modulus exclusion; no numerical oracle."""
import sympy as s,json
from fractions import Fraction as F
from math import isqrt,comb
from pathlib import Path
D=json.loads(Path(__file__).with_name('level35_positive_root_disks.json').read_text())
X=s.Symbol('XX');p=s.Poly(s.sympify(D['p']),X);fy=s.Poly(s.sympify(D['Y_of_X']),X);fz=s.Poly(s.sympify(D['Z_of_X']),X)
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
r=F(1,10**18);centers=[];report=[]
for disk in D['disks']:
 c=tuple(F(q) for q in disk['center']);r=F(disk['radius']);assert r==F(1,10**18);centers.append(c)
 ts=tay(coeffs(p),c);rest=norm(ts[0])[1]+sum(norm(ts[j])[1]*r**j for j in range(2,len(ts)))
 assert norm(ts[1])[0]*r>rest
 lo,hi=norm(c);lo-=r;hi+=r
 if hi<1:kind='X_inside_unit_circle'
 else:
  ys=tay(coeffs(fy),c);err=sum(norm(ys[j])[1]*r**j for j in range(1,len(ys)));yl,yh=norm(ys[0]);yl-=err;yh+=err
  if yh<1:kind='Y_inside_unit_circle'
  elif yl>hi**2:kind='Y_exceeds_X_squared'
  else:
   zs=tay(coeffs(fz),c);ze=sum(norm(zs[j])[1]*r**j for j in range(1,len(zs)));assert norm(zs[0])[1]+ze<1;kind='Z_inside_unit_circle'
 report.append({'center':[str(c[0]),str(c[1])],'radius':str(r),'exclusion':kind})
 print(float(c[0]),float(c[1]),kind,flush=True)
for i,c in enumerate(centers):
 for d in centers[i+1:]:assert norm((c[0]-d[0],c[1]-d[1]))[0]>2*r
assert len(report)==p.degree()
assert len(report)==15
print('EXACT ROOT EXCLUSION PASS')

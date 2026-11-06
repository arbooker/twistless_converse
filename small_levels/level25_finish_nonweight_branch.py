"""Explore full first-jet compatibility on the forced eta=-1 cusp branch.
Necessary determinant equations are computed exactly; no generic rank is
misreported as a uniform pole exclusion.
"""
import sys,time
from pathlib import Path
sys.argv=[sys.argv[0],'-1']
src=Path(__file__).with_name('level25_finish_firstjet.py').read_text()
exec(src[:src.index('constraints=[]')])
from sympy.polys.fields import field
from sympy import QQ,factor,Poly,gcd as pgcd
from functools import lru_cache
L,X,Z=field('X,Z',QQ)
images=[X,3*X/2,Z,1/X-X/2,2/(3*X)-4*X/3]
@lru_cache(None)
def ev(v):
 if v:
  np={(pw[1]+pw[4])%2 for pw,co in v.numer.terms()}
  dp={(pw[1]+pw[4])%2 for pw,co in v.denom.terms()}
  assert len(np)==1 and np==dp,('sign branch mismatch',v)
 def poly(p):
  ans=L.zero
  for pw,co in p.terms():
   term=L(co)
   for im,e in zip(images,pw):term*=im**e
   ans+=term
  return ans
 return poly(v.numer)/poly(v.denom)
assert free==[42,60,108,120,126]
# Unknowns u0,u2,u4 are old components scaled by z^2.
# Lower-point free components are v0,...,v4, with the same scaling.
vtop=[{0:1/Z**2},{8:-L(1)/2},{1:1/Z**2},{8:L.one},{2:1/Z**2}]
vlow=[{3:1/Z**2},{4:L.one},{5:1/Z**2},{6:L.one},{7:1/Z**2}]
def addterm(out,coef,vec):
 for j,w in vec.items():out[j]=out.get(j,L.zero)+coef*w
def clean(out):return {j:v for j,v in out.items() if v}
matrix=[]
for row,rid in R:
 out={}
 for i,c in enumerate(free):addterm(out,ev(row.get(c,K.zero)),vtop[i])
 if clean(out):matrix.append(clean(out))
 out={}
 for i,c in enumerate(free):
  addterm(out,ev(shift(row.get(c,K.zero))),vlow[i])
  addterm(out,-ev(sources[i][rid]),vtop[i])
 if clean(out):matrix.append(clean(out))
for rid in zeroids:
 out={}
 for i in range(5):addterm(out,ev(sources[i][rid]),vtop[i])
 if clean(out):matrix.append(clean(out))
print('BRANCH_MATRIX',len(matrix),'elapsed',time.time()-st,flush=True)
basis={};det=L.one;minors=[]
for rr in matrix:
 while any(j<8 for j in rr):
  j=min(j for j in rr if j<8)
  if j not in basis:
   val=rr[j];det*=val;basis[j]={i:v/val for i,v in rr.items()};break
  c=rr[j]
  for i,v in basis[j].items():
   rr[i]=rr.get(i,L.zero)-c*v
   if not rr[i]:del rr[i]
 else:
  if rr:
   val=det*rr[8]
   # Earlier residuals involve only the then-selected pivot rows: still
   # exact augmented minors, with no division by a parameter polynomial.
   assert len(val.denom.terms())==1,val
   p=val.numer.as_expr()
   minors.append(p);print('MINOR',factor(p),flush=True)
print('COEFFICIENT_RANK',len(basis),'MINORS',len(minors),flush=True)
assert len(det.denom.terms())==1,det
print('COEFFICIENT_MINOR',factor(det.numer.as_expr()),flush=True)
g=None
for p in minors:g=p if g is None else pgcd(g,p)
print('MINOR_GCD',factor(g) if g is not None else None,flush=True)

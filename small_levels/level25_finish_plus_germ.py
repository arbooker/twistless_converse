"""Explore full first-jet compatibility on the eta=+1 denominator-five cusp branch.
Necessary determinant equations are computed exactly; no generic rank is
misreported as a uniform pole exclusion.
"""
import sys,time
from pathlib import Path
sys.argv=[sys.argv[0],'1']
src=Path(__file__).with_name('level25_finish_firstjet.py').read_text()
exec(src[:src.index('constraints=[]')])
from sympy.polys.fields import field
from sympy import QQ,factor,Poly,gcd as pgcd
from functools import lru_cache
L,X,Y,Z=field('X,Y,Z',QQ)
images=[X,Y,Z,-X-2/X,-Y-3/Y]
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

assert free==[48,54,102,120]
# Form identities over the full parameter field BEFORE cusp-branch
# substitution. This eliminates all lower-point germs without a
# pole-order assumption or division by a vanishing parameter.
basis={};det=K.one;compat=[]
for row,rid in sorted(R,key=lambda pair:len(pair[0])):
 rr={i:shift(row.get(c,K.zero)) for i,c in enumerate(free) if row.get(c,K.zero)}
 bb=[sources[t][rid] for t in range(4)]
 while rr:
  j=min(rr)
  if j not in basis:
   val=rr[j];det*=val;basis[j]=({i:v/val for i,v in rr.items()},[v/val for v in bb]);break
  br,bs=basis[j];c=rr[j]
  bb=[v-c*w for v,w in zip(bb,bs)]
  for i,v in br.items():
   rr[i]=rr.get(i,K.zero)-c*v
   if not rr[i]:del rr[i]
 else:
  out=[det*v for v in bb]
  for v in out:assert not v or len(v.denom.terms())==1
  if any(out):compat.append(out)
print('GERM_IDENTITIES',len(compat),len(basis),flush=True)
# Highest top coefficient obeys leading rows and all germ identities.
cons=[[row.get(c,K.zero) for c in free] for row,rid in R]+compat
matrix=[]
for row in cons:
 rr={i:ev(v)*(Z**-2 if i<3 else 1) for i,v in enumerate(row) if v}
 rr={i:v for i,v in rr.items() if v}
 if rr:matrix.append(rr)
basis={};det=L.one;minors=[]
for rr in sorted(matrix,key=lambda row:len(row)):
 while any(j<3 for j in rr):
  j=min(j for j in rr if j<3)
  if j not in basis:
   val=rr[j];det*=val;basis[j]={i:v/val for i,v in rr.items()};break
  c=rr[j]
  for i,v in basis[j].items():
   rr[i]=rr.get(i,L.zero)-c*v
   if not rr[i]:del rr[i]
 else:
  if rr:
   val=det*rr[3]
   assert len(val.denom.terms())==1,val
   p=val.numer.as_expr();minors.append(p)
   print('GERM_MINOR',factor(p),flush=True)
g=None
for p in minors:g=p if g is None else pgcd(g,p)
print('GERM_GCD',factor(g),flush=True)

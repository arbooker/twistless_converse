"""Exclude a rightmost additive-twist pole at s0=k, uniformly in even k.

Run from the project root, optionally with eta delta (default -1 -1).
Reconstructs the leading matrix, derives an exact resultant, and checks
finite Abel-summation certificates. Uses SymPy and exact integers only.
"""
from pathlib import Path
import sys,math
from fractions import Fraction
source=Path(__file__).with_name('level19_pole_probe.py').read_text()
exec(source[source.index('import sys,time'):source.index('pivs,jrows=elim(jet,Q)')])
pivs,rem=elim(original,Q)
assert len(pivs)==111
J=x**4+(a*a-2)*x*x+1;vv=[-J,x*a*(y*y+1),-x*a*(y*y+1)]
ps=[]
for rr,ll in rem:
 p=sum((rr.get(j,K.zero)*v for j,v in zip([18,42,72],vv)),K.zero)
 if p and p.numer not in ps:ps.append(p.numer)
import sympy as sp
X,Y,Z,A,B=sp.symbols('X Y Z A B');new=[];whole=[]
for p in ps:
 terms=p.terms();dx=min(pw[0]-pw[3] for pw,cf in terms);dy=min(pw[1]-pw[4] for pw,cf in terms)
 dd={}
 for pw,cf in terms:
  assert (pw[0]-pw[3]-dx)%2==0 and (pw[1]-pw[4]-dy)%2==0
  dd[((pw[0]-pw[3]-dx)//2,(pw[1]-pw[4]-dy)//2,pw[2],pw[3],pw[4])]=cf
 pp=sp.Poly.from_dict(dd,(X,Y,Z,A,B)).monic().as_expr()
 whole.append(pp)
 for f,e in sp.factor_list(pp)[1]:
  if f not in new and len(str(f))>30:new.append(f)
new.sort(key=lambda p:len(sp.Poly(p,X,Y,Z,A,B).terms()))
assert all(sp.Poly(p,X,Y,Z,A,B).monic().as_expr() in whole for p in new[:2])
assert not new[0].has(Z) and not new[1].has(Z)
assert sp.degree(new[0],B)==1 and sp.degree(new[1],B)==2
factors=sp.factor_list(sp.resultant(new[0],new[1],B))[1]
large=[f for f,e in factors if len(str(f))>100]
assert len(large)==1
for f,e in factors:
 if f!=large[0]:assert f==Y+1
terms=sp.Poly(large[0],X,Y,A).terms();assert len(terms)==243
coeffs={}
for (i,j,r),cf in terms:
 for t in range(r+1):
  alpha=4**i*9**j*2**r;beta=4**(i+t)*9**j
  key=(alpha,beta)
  coeffs[key]=coeffs.get(key,0)+Fraction(cf)*(-1)**r*math.comb(r,t)
coeffs={p:c for p,c in coeffs.items() if c}
alphas=sorted({p[0] for p in coeffs});betas=sorted({p[1] for p in coeffs})
assert (len(coeffs),len(alphas),len(betas))==(487,90,58)
# Shift by (2,2). Every upper-right cumulative sum is strictly negative.
cum=[[0]*(len(betas)+1) for _ in range(len(alphas)+1)]
for i in reversed(range(len(alphas))):
 for j in reversed(range(len(betas))):
  al,be=alphas[i],betas[j]
  cum[i][j]=coeffs.get((al,be),0)*al**2*be**2+cum[i+1][j]+cum[i][j+1]-cum[i+1][j+1]
  assert cum[i][j]<0
# Fixed n=0,1 or fixed ell=0,1, respectively.
for axis,fixed,shift in [(0,0,1),(0,1,1),(1,0,3),(1,1,2)]:
 co={}
 for (al,be),c in coeffs.items():
  base=be if axis==0 else al;weight=al**fixed if axis==0 else be**fixed
  co[base]=co.get(base,0)+c*weight
 co={p:c for p,c in co.items() if c};running=0
 for base in sorted(co,reverse=True):
  running+=co[base]*base**shift
  assert running<0
 for j in range(shift):assert sum(c*base**j for base,c in co.items())!=0
print('Verified uniform exclusion of s0=k for signs',eta,bad)
print('Certificate: 5220 negative double cumulative sums and four boundary strips.')

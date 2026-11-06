"""Exact exclusion of s=k poles for N21, except a single weight-2 case.
For each sign triple, a resultant has a unique largest exponential base252.
Its term dominates for n=k/2>=2; n=1 is checked exactly.
"""
from pathlib import Path
src=Path(__file__).with_name('level21_augmented_first_jet.py').read_text()
exec(src[:src.index('def rhs(lab):')])
from sympy import symbols,resultant,factor,groebner
xx,yy,zz,aa=symbols('x y z a')
ps=[list(r.values())[0].numer.as_expr() for r,l in R]

from sympy import Poly,factor_list
for pp in ps[1:]:
 rr=resultant(ps[0],pp,aa)
 if rr!=0:break
print('signs',eta,bad3,bad7,'resultant',factor(rr))
for f,e in factor_list(rr)[1]:
 if len(Poly(f,xx,yy,zz).terms())==1:continue
 bases={}
 for (i,j,k),c in Poly(f,xx,yy,zz).terms():
  base=2**i*3**j*7**k;bases[base]=bases.get(base,0)+c
 bases={b:c for b,c in bases.items() if c}
 top=max(bases);lead=abs(bases[top]);rest={b:abs(c) for b,c in bases.items() if b!=top}
 cutoff=next((n for n in range(1,15) if sum(c*b**n for b,c in rest.items())<lead*top**n),None)
 print('factor',f,'top',top,'cutoff',cutoff,'small',[(n,sum(c*b**n for b,c in bases.items())) for n in range(1,cutoff or 5)])

 assert top==252 and cutoff==2
 zeros=[n for n in range(1,cutoff) if sum(c*b**n for b,c in bases.items())==0]
 assert zeros==([1] if (eta,bad3,bad7)==(-1,-1,1) else [])
 if zeros:
  from sympy import Rational
  vals=[pp.subs({xx:2,yy:3,zz:7}) for pp in ps]
  assert all(v.subs(aa,Rational(-3,2))==0 for v in vals)
  assert any(Poly(v,aa).degree()==1 for v in vals)
print('WEIGHT_POLE_CERTIFICATE_VERIFIED',eta,bad3,bad7)

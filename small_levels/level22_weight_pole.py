"""Exact exclusion of s=k residues, except one explicit weight-2 case.

Run once for each ETA BAD2 BAD11 sign triple.  The assertion bounds every
integer n=k/2 >=3 by the largest exponential term, and checks n=1,2.
This does not prove the missing modular transformation identities.
"""
from pathlib import Path
src=Path(__file__).with_name('level22_pole_kernel.py').read_text()
exec(src[:src.index("print('monomial rank'")])
from sympy import Poly,symbols,resultant,factor,factor_list
xx,yy,zz,aa=symbols('x y z a')
ps=[list(r.values())[0].numer.as_expr() for r,l in R]
factors=[]
for pp in ps[1:]:
 rr=resultant(ps[0],pp,aa)
 if rr!=0:
  factors=factor_list(rr)[1];break
print('signs',eta,bad2,bad11)
for f,e in factors:
 if len(Poly(f,xx,yy,zz).terms())==1:continue
 print('factor',factor(f))
 bases={}
 for (i,j,k),c in Poly(f,xx,yy,zz).terms():
  b=2**i*3**j*11**k;bases[b]=bases.get(b,0)+c
 bases={b:c for b,c in bases.items() if c}
 top=max(bases);lead=abs(bases[top]);rest={b:abs(c) for b,c in bases.items() if b!=top}
 if top==5832:
  e,u,t=eta,bad2,eta*bad2*bad11
  expected=(2*xx**8+u*xx**7*yy**2+u*xx**7+xx**6-2*u*xx**5*yy**2-3*u*xx**5+xx**4*yy**4-e*u*xx**4*yy**2*zz+(2-t)*xx**4*yy**2-xx**4
    +u*xx**3*yy**6+2*u*xx**3*yy**4-e*xx**3*yy**2*zz+u*(1-t)*xx**3*yy**2-u*xx**3+3*xx**2*yy**6-e*u*xx**2*yy**2*zz+(3-t)*xx**2*yy**2+xx**2
    +u*xx*yy**6-3*u*xx*yy**4-2*u*xx*yy**2-e*u*yy**4*zz-t*yy**4)
  assert __import__('sympy').expand(f-expected)==0
 cutoff=next((n for n in range(1,12) if sum(c*b**n for b,c in rest.items()) < lead*top**n),None)
 print('leading',top,bases[top],'cutoff',cutoff,'valuesbelow',[(n,sum(c*b**n for b,c in bases.items())) for n in range(1,cutoff or 5)],flush=True)
 assert cutoff==1 or cutoff==3
 zeros=[n for n in range(1,cutoff) if sum(c*b**n for b,c in bases.items())==0]
 assert zeros==([1] if (eta,bad2,bad11)==(-1,-1,1) and top==5832 else [])
 if zeros:
  vals=[pp.subs({xx:2,yy:3,zz:11}) for pp in ps]
  assert all(v.subs(aa,__import__('sympy').Rational(-7,3))==0 for v in vals)
  assert any(Poly(v,aa).degree()==1 for v in vals)
print('WEIGHT_POLE_EXCLUSION_VERIFIED',eta,bad2,bad11)

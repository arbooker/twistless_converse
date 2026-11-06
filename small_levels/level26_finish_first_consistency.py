"""Exact exploratory leading/first-jet reduction for N26.
A nonzero minor proves continuation; its zeros still require pole analysis.
"""
from pathlib import Path
import os
exec(Path(__file__).with_name('level26_jet_builder.py').read_text().replace('N=26;Q=78','N=26;Q='+os.environ.get('N26_GRID','78')))
original=[(dict(row),lab) for row,lab in R]
R=[(dict(row),i) for i,(row,lab) in enumerate(original)]
def safe(v):
 return len(v.numer.terms())==len(v.denom.terms())==1 and not any(v.numer.terms()[0][0][3:]) and not any(v.denom.terms()[0][0][3:])
def shift(v,n=1):
 def poly(p):return K(K.ring.from_dict({pw:cf/(2**(n*pw[0])*3**(n*pw[1])*13**(n*pw[2])) for pw,cf in p.terms()}))
 return poly(v.numer)/poly(v.denom)
piv=[];operations=[];zeroids=[]
while R:
 choices=[i for i,(r,l) in enumerate(R) if any(safe(v) for v in r.values())]
 if not choices:break
 ii=min(choices,key=lambda i:len(R[i][0]));row,rid=R.pop(ii)
 j=min((j for j,v in row.items() if safe(v)),key=lambda j:sum(j in rr for rr,ll in R))
 val=row[j];row={c:v/val for c,v in row.items()};piv.append((j,row,rid));updates=[];new=[]
 for rr,rid2 in R:
  if j in rr:
   v=rr[j];updates.append((rid2,v))
   for c,u in row.items():
    rr[c]=rr.get(c,K.zero)-v*u
    if not rr[c]:del rr[c]
  if rr:new.append((rr,rid2))
  else:zeroids.append(rid2)
 operations.append((rid,val,updates));R=new
free=[j for j in range(Q) if j not in [j for j,row,rid in piv]]
print('rank',len(piv),'free',free,flush=True)
assert len(free)>=2
kernels=[];sources=[]
for col in free:
 pole=[K.zero]*Q;pole[col]=K.one
 for j,row,rid in reversed(piv):pole[j]=-sum((v*pole[c] for c,v in row.items() if c!=j),K.zero)
 kernels.append(pole)
 def rhs(lab):
  if lab[0]=='g':
   _,A,B,C,D,mu,j=lab;den=C*j+D*Q;beta=Q*(A*j+B*Q)//den%Q;det=A*D-B*C
   return shift(mu*mon(Fraction(den*den,det*Q*Q)))*K(Fraction(C*den,det*Q))*pole[beta]
  if lab[0]=='F':
   _,q,t=lab;ell=lcm(N,q*q);u=-(Q*Q//ell)//t
   leading=eta*(-bad2 if q%2==0 else 1)*(-bad13 if q%13==0 else 1)*mon(Fraction(ell*t*t,Q*Q))
   off=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
   return shift(leading)*K(Fraction(ell*t,Q))*sum((pole[(j+u)%Q] for j in off),K.zero)
  return K.zero
 bvec=[rhs(lab) for row,lab in original]
 for rid,val,updates in operations:
  bvec[rid]/=shift(val)
  for rid2,coef in updates:bvec[rid2]-=shift(coef)*bvec[rid]
 sources.append(bvec)
lead=list(dict.fromkeys(tuple(row.get(j,K.zero) for j in free) for row,rid in R))
jet=list(dict.fromkeys(tuple(col[rid] for col in sources) for rid in zeroids if any(col[rid] for col in sources)))
print('free',free,'lead_count',len(lead),'zero-row jets',len(jet),flush=True)
from sympy import factor,gcd as poly_gcd
extra=[]
for ii,(row,rid) in enumerate(R if os.environ.get('N26_EXTRA') else []):
 for rr,rid2 in R[ii+1:]:
  j=next(iter(row))
  # Cross-multiply residual lower-point leading rows; no division.
  if all(shift(row.get(c,K.zero))*shift(rr[j])==shift(rr.get(c,K.zero))*shift(row[j]) for c in free):
   e=tuple(col[rid]*shift(rr[j])-col[rid2]*shift(row[j]) for col in sources)
   if any(e):extra.append(e)
constraints=lead+jet+extra
active=[i for i in range(len(free)) if any(row[i] for row in constraints)]
print('active positions',[free[i] for i in active],flush=True)
assert len(active)==2
constraints=[tuple(row[i] for i in active) for row in constraints]
def normalize_row(row):
 terms=[]
 for v in row:
  if not v:continue
  assert len(v.denom.terms())==1
  dp,dc=v.denom.terms()[0]
  terms.extend((tuple(p[i]-dp[i] for i in range(3)),Fraction(int(c.numerator),int(c.denominator))/Fraction(int(dc.numerator),int(dc.denominator))) for p,c in v.numer.terms())
 mins=[min(p[i] for p,c in terms) for i in range(3)]
 coeff=Fraction(reduce(gcd,(abs(c.numerator) for p,c in terms)),reduce(lcm,(c.denominator for p,c in terms)))
 if terms[0][1]<0:coeff=-coeff
 scale=K(coeff)*x**mins[0]*y**mins[1]*z**mins[2]
 return tuple(v/scale for v in row)
constraints=list(dict.fromkeys(normalize_row(row) for row in constraints if any(row)))
print('normalized constraints',len(constraints),flush=True)
common=None
minors=set()
for i,r in enumerate(constraints):
 for t in constraints[i+1:]:
  det=r[0]*t[1]-r[1]*t[0]
  if det:
   expr=det.numer.as_expr();minors.add(expr);common=expr if common is None else poly_gcd(common,expr)
print('extra_count',len(extra),'minor gcd',factor(common) if common is not None else None,flush=True)

import json
out=os.environ.get('N26_OUT')
if out:
 Path(out).write_text(json.dumps({'signs':[eta,bad2,bad13],'Q':Q,'free':free,'active':[free[i] for i in active], 'constraints':[[str(v) for v in row] for row in constraints],'minors':[str(v) for v in minors]},indent=2))
if os.environ.get('N26_GB'):
 from sympy import groebner,symbols,Poly
 v=symbols('a x y z');clean=[]
 for f in minors:
  pol=Poly(f,*v);mm=[min(p[i] for p,c in pol.terms()) for i in range(4)]
  clean.append(f/(v[1]**mm[1]*v[2]**mm[2]*v[3]**mm[3]))
 print('distinct minors',len(minors),flush=True)
 gg=groebner(clean,*v)
 print('Groebner',gg,flush=True)

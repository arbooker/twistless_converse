"""Exact exploratory two-coordinate leading/first-jet reduction for N28.
A nonzero minor proves continuation; its zeros still require pole analysis.
"""
from pathlib import Path
exec(Path(__file__).with_name('level28_jet_builder.py').read_text())
original=[(dict(row),lab) for row,lab in R]
R=[(dict(row),i) for i,(row,lab) in enumerate(original)]
def safe(v):
 return len(v.numer.terms())==len(v.denom.terms())==1 and not any(v.numer.terms()[0][0][3:]) and not any(v.denom.terms()[0][0][3:])
def shift(v,n=1):
 def poly(p):return K(K.ring.from_dict({pw:cf/(2**(n*pw[0])*3**(n*pw[1])*7**(n*pw[2])) for pw,cf in p.terms()}))
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
assert len(free)==2
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
   leading=eta*(-bad7 if q%7==0 else 1)*mon(Fraction(ell*t*t,Q*Q))
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
print('free',free,'lead',lead,'zero-row jets',jet,flush=True)
from sympy import factor,gcd as poly_gcd
constraints=lead+jet
common=None
for i,r in enumerate(constraints):
 for t in constraints[i+1:]:
  det=r[0]*t[1]-r[1]*t[0]
  if det:
   expr=det.numer.as_expr();common=expr if common is None else poly_gcd(common,expr)
print('minor gcd',factor(common) if common is not None else None,flush=True)

"""Exact first-Taylor obstruction certificate for N21.
Uses division-free elimination of the remaining lower-pole parameter.
All eight sign cases are checked against an explicit reduced ideal.
The analytic interpretation is in level21_poles.tex.
"""
from pathlib import Path
exec(Path(__file__).with_name('level21_augmented_builder.py').read_text())
original=[(dict(row),lab) for row,lab in R]
R=[(dict(row),i) for i,(row,lab) in enumerate(original)]
def safe(v):
 return len(v.numer.terms())==len(v.denom.terms())==1 and not any(v.numer.terms()[0][0][3:]) and not any(v.denom.terms()[0][0][3:])
def shift(v,n=1):
 def poly(p):return K(K.ring.from_dict({powers:coef/(2**(n*powers[0])*3**(n*powers[1])*7**(n*powers[2])) for powers,coef in p.terms()}))
 return poly(v.numer)/poly(v.denom)
piv=[];operations=[];zeroids=[];start=time.time()
while R:
 choices=[i for i,(r,l) in enumerate(R) if any(safe(v) for v in r.values())]
 if not choices:break
 ii=min(choices,key=lambda i:len(R[i][0]));row,rid=R.pop(ii)
 j=min((j for j,v in row.items() if safe(v)),key=lambda j:sum(j in rr for rr,ll in R))
 val=row[j];row={c:v/val for c,v in row.items()};piv.append((j,row,rid));updates=[]
 new=[]
 for rr,rid2 in R:
  if j in rr:
   v=rr[j];updates.append((rid2,v))
   for c,u in row.items():
    rr[c]=rr.get(c,K.zero)-v*u
    if not rr[c]:del rr[c]
  if rr:new.append((rr,rid2))
  else:zeroids.append(rid2)
 operations.append((rid,val,updates));R=new
 if time.time()-start>45:raise TimeoutError
free=[j for j in range(Q) if j not in [j for j,row,rid in piv]]
assert len(free)==1,free
print('monomial rank',len(piv),'free',free,'residual',len(R),flush=True)
pole=[K.zero]*Q;pole[free[0]]=K.one
for j,row,rid in reversed(piv):pole[j]=-sum((v*pole[c] for c,v in row.items() if c!=j),K.zero)
def rhs(lab):
 if lab[0]=='g':
  _,A,B,C,D,mu,j=lab;den=C*j+D*Q;beta=Q*(A*j+B*Q)//den%Q;det=A*D-B*C
  leading=mu*mon(Fraction(den*den,det*Q*Q))
  return shift(leading)*K(Fraction(C*den,det*Q))*pole[beta]
 if lab[0]=='F':
  _,q,t=lab;ell=lcm(N,q*q);d=Q*Q//ell;u=-d//t
  eta_q=eta*(-bad3 if q%3==0 else 1)*(-bad7 if q%7==0 else 1)
  leading=eta_q*mon(Fraction(ell*t*t,Q*Q))
  off=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
  return shift(leading)*K(Fraction(ell*t,Q))*sum((pole[(j+u)%Q] for j in off),K.zero)
 return K.zero
bvec=[rhs(lab) for row,lab in original]
for rid,val,updates in operations:
 bvec[rid]/=shift(val)
 for rid2,coef in updates:bvec[rid2]-=shift(coef)*bvec[rid]
print('rhs reduced',round(time.time()-start,2),flush=True)
from sympy import factor,groebner,symbols
obs=[]
for rid in zeroids:
 if bvec[rid]:
  expr=factor(bvec[rid].numer.as_expr());print(original[rid][1],expr,flush=True);obs.append(expr)
print('zero-row obstruction count',len(obs),flush=True)
assert all(set(row)==set(free) for row,rid in R)
lead=[next(iter(row.values())).numer.as_expr() for row,rid in R]
G=groebner(lead+obs,*symbols('a x y z'))
print('zero-row plus leading GB',G,flush=True)


xx,yy,zz,aa=symbols('x y z a')
expected=groebner([aa*xx+xx**2-1,yy+3*bad3,zz-eta*bad3*(6+eta*bad3*bad7)],aa,xx,yy,zz)
assert G==expected,(G,expected)
print('FIRST_JET_CERTIFICATE_VERIFIED',eta,bad3,bad7)

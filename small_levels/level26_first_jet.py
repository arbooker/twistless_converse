"""Uniform N26 continuation certificate using a shifted first-Taylor syzygy.
No pole-cancellation or modularity claim."""
from pathlib import Path
exec(Path(__file__).with_name("level26_jet_builder.py").read_text())
original=[(dict(row),lab) for row,lab in R]
R=[(dict(row),i) for i,(row,lab) in enumerate(original)]
def audit(poly):
 groups={}
 for powers,coef in poly.terms():
  groups.setdefault(powers[:3],[]).append(powers[3:])
 return any(len(t)==1 and not any(t[0]) for t in groups.values())
def safe(v):return audit(v.numer) and audit(v.denom)
def shift(v,n=1):
 def poly(p):return K(K.ring.from_dict({powers:coef/(2**(n*powers[0])*3**(n*powers[1])*13**(n*powers[2])) for powers,coef in p.terms()}))
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
assert len(piv)==77 and not R
print('leading rank',len(piv),'free',free,'residual',len(R),flush=True)
pole=[K.zero]*Q;pole[free[0]]=K.one
for j,row,rid in reversed(piv):pole[j]=-sum((v*pole[c] for c,v in row.items() if c!=j),K.zero)
assert all(sum((v*pole[j] for j,v in row.items()),K.zero)==0 for row,lab in original)
def rhs(lab):
 if lab[0]=='g':
  _,A,B,C,D,mu,j=lab;den=C*j+D*Q;beta=Q*(A*j+B*Q)//den%Q;det=A*D-B*C
  leading=mu*mon(Fraction(den*den,det*Q*Q))
  return shift(leading)*K(Fraction(C*den,det*Q))*pole[beta]
 if lab[0]=='F':
  _,q,t=lab;ell=lcm(N,q*q);d=Q*Q//ell;u=-d//t
  eta_q=eta*(-bad2 if q%2==0 else 1)*(-bad13 if q%13==0 else 1)
  leading=eta_q*mon(Fraction(ell*t*t,Q*Q))
  off=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
  return shift(leading)*K(Fraction(ell*t,Q))*sum((pole[(j+u)%Q] for j in off),K.zero)
 return K.zero
bvec=[rhs(lab) for row,lab in original]
for rid,val,updates in operations:
 bvec[rid]/=shift(val)
 for rid2,coef in updates:bvec[rid2]-=shift(coef)*bvec[rid]
print('rhs reduced',round(time.time()-start,2),flush=True)
import json
valid=[rid for rid in zeroids if bvec[rid] and audit(bvec[rid].numer) and audit(bvec[rid].denom)]
assert valid, 'No uniformly nonzero first-jet obstruction'
rid=valid[0]
result={'N':N,'Q':Q,'eta':eta,'bad2':bad2,'bad13':bad13,'leading_rank':len(piv),'augmented_rank':Q,'label':original[rid][1],'obstruction':str(bvec[rid]),'all_complex_lambda3':True}
print(json.dumps(result),flush=True)
print('UNIFORM_FIRST_JET_CONTINUATION_VERIFIED',flush=True)

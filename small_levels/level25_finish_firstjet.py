"""Exact first-jet compatibility at a highest pole s0 != k for N25.

No pole claim is made unless the printed residual obstruction is proved
nonzero.  Dividing by the scalar s0-k is legitimate only in that case.
All algebraic pivots used here are nonzero Laurent monomials independent
of the arbitrary eigenvalues a,b. Scratch data are written to /tmp.
"""
import sys,time,json
from pathlib import Path
base=Path(__file__).parent
exec((base/'level25_finish_augmented.py').read_text())
original=[(dict(row),lab) for row,lab in R]
R=[(dict(row),i) for i,(row,lab) in enumerate(original)]
def safe(v):
 return (len(v.numer.terms())==len(v.denom.terms())==1
   and not any(v.numer.terms()[0][0][3:])
   and not any(v.denom.terms()[0][0][3:]))
def shift(v):
 def poly(p):
  return K(K.ring.from_dict({pw:co/(2**pw[0]*3**pw[1]*5**pw[2]) for pw,co in p.terms()}))
 return poly(v.numer)/poly(v.denom)
piv=[];operations=[];zeroids=[];st=time.time()
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
 if time.time()-st>60:raise TimeoutError
free=sorted(set(range(Q))-{j for j,row,rid in piv})
print('LEADING',eta,len(piv),free,len(R),len(zeroids),flush=True)
poles=[]
for fc in free:
 pole=[K.zero]*Q;pole[fc]=K.one
 for j,row,rid in reversed(piv):pole[j]=-sum((v*pole[c] for c,v in row.items() if c!=j),K.zero)
 poles.append(pole)
def rhs(lab,pole):
 if lab[0]=='g':
  _,A,B,C,D,mu,j=lab;den=C*j+D*Q;beta=Q*(A*j+B*Q)//den%Q;det=A*D-B*C
  leading=mu*mon(Fraction(den*den,det*Q*Q))
  return leading*K(Fraction(C*Q,den))*pole[beta]
 if lab[0]=='F':
  _,q,t=lab;ell=lcm(N,q*q);d=Q*Q//ell;u=-d//t
  leading=eta*mon(Fraction(ell*t*t,Q*Q));off=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
  return leading*K(Fraction(Q,t))*sum((pole[(j+u)%Q] for j in off),K.zero)
 return K.zero
sources=[]
for pole in poles:
 bvec=[rhs(lab,pole) for row,lab in original]
 for rid,val,updates in operations:
  bvec[rid]/=shift(val)
  for rid2,coef in updates:bvec[rid2]-=shift(coef)*bvec[rid]
 sources.append(bvec)
print('FIRST_JETS',round(time.time()-st,2),flush=True)
constraints=[]
for row,rid in R:constraints.append(({i:row[c] for i,c in enumerate(free) if c in row},('lead',original[rid][1])))
for rid in zeroids:
 v={t:sources[t][rid] for t in range(len(free)) if sources[t][rid]}
 if v:constraints.append((v,('jet',original[rid][1])))
print('NONZERO_CONSTRAINTS',len(constraints),flush=True)
cp=[];R=constraints
while R:
 choices=[i for i,(r,l) in enumerate(R) if any(safe(v) for v in r.values())]
 if not choices:break
 ii=min(choices,key=lambda i:len(R[i][0]));row,lab=R.pop(ii)
 j=min((j for j,v in row.items() if safe(v)),key=lambda j:sum(j in rr for rr,ll in R))
 val=row[j];row={c:v/val for c,v in row.items()};cp.append((j,row,lab));new=[]
 for rr,ll in R:
  if j in rr:
   v=rr[j]
   for c,u in row.items():
    rr[c]=rr.get(c,K.zero)-v*u
    if not rr[c]:del rr[c]
  if rr:new.append((rr,ll))
 R=new
print('JET_MONOMIAL_RANK',len(cp),'OUT_OF',len(free),'REMAINING',len(R),flush=True)
print('JET_PIVOTS',[(j,{c:str(v) for c,v in row.items()},lab) for j,row,lab in cp],flush=True)
print('DENOMINATOR5', {j:[str(pole[j]) for pole in poles] for j in range(Q//5,Q,Q//5)},flush=True)
from sympy import factor
out=[];seen=set()
for rr,lab in R:
 v={i:str(factor(c.as_expr())) for i,c in rr.items()};key=tuple(v.items())
 if key not in seen:seen.add(key);out.append((v,lab))
print('DISTINCT',len(out),flush=True)
for row,lab in out:print(lab,row,flush=True)
Path('/tmp/level25_finish_firstjet_%s.json'%eta).write_text(json.dumps({'eta':eta,'free':free,'rank':len(cp),'rows':out}))

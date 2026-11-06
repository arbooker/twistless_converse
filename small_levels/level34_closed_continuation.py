"""Uniform continuation of90 closed coordinates in the102-grid at N34.
Includes every /3 and /34 additive twist. Uses the modulus-six elliptic law.
"""
from pathlib import Path
exec(Path(__file__).with_name('level34_jet_builder.py').read_text())
U=set(range(Q))-{11,23,28,31,37,40,62,65,71,74,79,91}
def closed(row,lab):
 if not set(row)<=U:return False
 if lab[0]=='g':
  _,A,B,C,D,mu,j=lab;den=C*j+D*Q
  return j in U and (Q*(A*j+B*Q)//den)%Q in U
 if lab[0]=='F':
  _,q,t=lab;ell=lcm(N,q*q);u=-(Q*Q//ell)//t
  off=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
  return all((j+t)%Q in U and (j+u)%Q in U for j in off)
 return True
R=[(row,lab) for row,lab in R if closed(row,lab)]
print('closedU',len(U),'rows',len(R),flush=True)
original=[(dict(row),lab) for row,lab in R]
R=[(dict(row),i) for i,(row,lab) in enumerate(original)]
def audit(poly):
 groups={}
 for powers,coef in poly.terms():
  groups.setdefault(powers[:3],[]).append(powers[3:])
 return any(len(t)==1 and not any(t[0]) for t in groups.values())
def safe(v):return audit(v.numer) and audit(v.denom)
def shift(v,n=1):
 def poly(p):return K(K.ring.from_dict({powers:coef/(2**(n*powers[0])*3**(n*powers[1])*17**(n*powers[2])) for powers,coef in p.terms()}))
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
free=[j for j in sorted(U) if j not in [j for j,row,rid in piv]]

print('free',free,'rank',len(piv),'remaining',len(R),flush=True)

assert len(U)==90 and len(piv)==90 and not free and not R
assert all(j in U for q in [3,34] for j in range(0,Q,Q//q))
import json
result={'N':N,'Q':Q,'U':sorted(U),'eta':eta,'bad2':bad2,'bad17':bad17,'all_complex_lambda3':True,'rank':len(piv),'pivots':[(j,str(val),original[rid][1]) for (j,row,rid),(rid2,val,updates) in zip(piv,operations)]}
Path('/tmp/level34_closed_case.json').write_text(json.dumps(result))
print('N34_CLOSED_CONTINUATION_VERIFIED',eta,bad2,bad17)

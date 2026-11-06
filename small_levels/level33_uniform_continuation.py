"""Uniform66-grid continuation at N33 using the modulus-six elliptic law.
All pivot coefficients include a parameter-independent exponential term.
"""
from pathlib import Path
exec(Path(__file__).with_name('level33_jet_builder.py').read_text())
original=[(dict(row),lab) for row,lab in R]
R=[(dict(row),i) for i,(row,lab) in enumerate(original)]
def audit(poly):
 groups={}
 for powers,coef in poly.terms():
  groups.setdefault(powers[:3],[]).append(powers[3:])
 return any(len(t)==1 and not any(t[0]) for t in groups.values())
def safe(v):return audit(v.numer) and audit(v.denom)
def shift(v,n=1):
 def poly(p):return K(K.ring.from_dict({powers:coef/(2**(n*powers[0])*3**(n*powers[1])*11**(n*powers[2])) for powers,coef in p.terms()}))
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

print('free',free,'rank',len(piv),'remaining',len(R),flush=True)

assert len(piv)==Q and not free and not R
import json
result={'N':N,'Q':Q,'eta':eta,'bad3':bad3,'bad11':bad11,'all_complex_lambda2':True,'rank':len(piv),'pivots':[(j,str(val),original[rid][1]) for (j,row,rid),(rid2,val,updates) in zip(piv,operations)]}
Path('/tmp/level33_continuation_case.json').write_text(json.dumps(result))
print('N33_UNIFORM_CONTINUATION_VERIFIED',eta,bad3,bad11)

"""Leading-only 204-pivot reduction, using only Laurent-monomial units.
Run -1 -1 -1 or 1 -1 -1 for the two sign-product classes.
"""
from pathlib import Path
import sys
src=Path(__file__).with_name('level35_full_continuation.py').read_text().split('def audit(poly):')[0]
n=0

exec(src)
def safe(v):
 return len(v.numer.terms())==len(v.denom.terms())==1 and not any(v.numer.terms()[0][0][4:]) and not any(v.denom.terms()[0][0][4:])
piv=[];start=time.time()
while R:
 choices=[i for i,(r,l) in enumerate(R) if any(safe(v) for v in r.values())]
 if not choices:break
 ii=min(choices,key=lambda i:len(R[i][0]));row,label=R.pop(ii)
 j=min((j for j,v in row.items() if safe(v)),key=lambda j:sum(j in rr for rr,ll in R))
 val=row[j];row={c:v/val for c,v in row.items()};piv.append((j,row,label));new=[]
 for rr,ll in R:
  if j in rr:
   v=rr[j]
   for c,u in row.items():
    rr[c]=rr.get(c,K.zero)-v*u
    if not rr[c]:del rr[c]
  if rr:new.append((rr,ll))
 R=new
 if time.time()-start>180:raise TimeoutError
free=sorted(set(range(Q))-{j for j,_,_ in piv})
target={70:K.one,140:-K.one}
for j,row,label in piv:
 if j in target:
  v=target[j]
  for c,u in row.items():
   target[c]=target.get(c,K.zero)-v*u
   if not target[c]:del target[c]
print('shift',n,'rank',len(piv),'free',free,'residualrows',len(R),'chi3target',target,flush=True)
import json
Path('/tmp/level35_leading_positive.json' if eta==1 else '/tmp/level35_leading_generic.json').write_text(json.dumps({'n':n,'free':free,'rows':[{str(j):str(v) for j,v in row.items()} for row,ll in R],'target':{str(j):str(v) for j,v in target.items()}}))

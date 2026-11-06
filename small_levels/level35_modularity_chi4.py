"""Exact leading-only 420-grid certificate after chi3 entireness.
Run ETA BAD5 BAD7. Every pivot is a Laurent-monomial unit independent of
Hecke eigenvalues. Residual coefficient is (zw-sigma5*sigma7)/(zw),
and the chi4 additive difference reduces to zero identically.
"""
from pathlib import Path
import sys,json,time
src=Path(__file__).with_name('level35_full_continuation.py').read_text().split('def audit(poly):')[0]
src=src.replace('Q=210','Q=420').replace('U=set(range(210))','U=set(range(420))')
src=src.replace("gens.append(((6,-1,-35,6),1))","gens.extend([((6,-1,-35,6),1),((3,-1,-35,12),1),((3,1,35,12),1),((41,-17,70,-29),1)])")
src=src.replace('range(3):','range(2):')
assert 'Q=420' in src and 'U=set(range(420))' in src
exec(src)
assert Q==420 and U==set(range(420))
assert R and all(set(row)<=U for row,label in R)
print('ROWS',len(R),flush=True)
def unit(v):return len(v.numer.terms())==len(v.denom.terms())==1 and not any(v.numer.terms()[0][0][4:]) and not any(v.denom.terms()[0][0][4:])
piv=[];start=time.time()
while R:
 candidates=[(len(r),i) for i,(r,l) in enumerate(R) if any(unit(v) for v in r.values())]
 if not candidates:break
 _,i=min(candidates);row,ll=R.pop(i);j=min((j for j,v in row.items() if unit(v)),key=lambda j:sum(j in r for r,_ in R));val=row[j];row={k:v/val for k,v in row.items()};piv.append((j,row));new=[]
 for r,l in R:
  if j in r:
   v=r[j]
   for k,u in row.items():
    r[k]=r.get(k,K.zero)-v*u
    if not r[k]:r.pop(k,None)
  if r:new.append((r,l))
 R=new
 if len(piv)%40==0:print('rank',len(piv),'rows',len(R),'time',round(time.time()-start,1),flush=True)
 if time.time()-start>240:raise TimeoutError
free=sorted(set(range(Q))-{j for j,row in piv});target={105:K.one,315:-K.one}
for j,row in piv:
 if j in target:
  v=target[j]
  for k,u in row.items():
   target[k]=target.get(k,K.zero)-v*u
   if not target[k]:target.pop(k,None)
assert len(piv)==419 and len(free)==1 and not target
expected=(z*w-K(bad5*bad7))/(z*w)
assert R and all(set(row)==set(free) and row[free[0]] in [expected,-expected] for row,label in R)
print('LEVEL35_CHI4_LEADING_PASS',eta,bad5,bad7,'rank',len(piv),'free',free,'target zero',flush=True)
Path('/tmp/level35_modularity_chi4_'+''.join('p' if e==1 else 'm' for e in (eta,bad5,bad7))+'.json').write_text(json.dumps({'free':free,'rows':[{str(j):str(v) for j,v in r.items()} for r,l in R],'target':{str(j):str(v) for j,v in target.items()}}))

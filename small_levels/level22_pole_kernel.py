"""Exploratory residual leading pole system after only monomial pivots.
No pole cancellation claim is made by this script.
"""
from pathlib import Path
src=Path(__file__).with_name('level22_uniform_continuation.py').read_text()
exec(src[:src.index('piv=[];start=time.time()')])
def mono_safe(v):
 return len(v.numer.terms())==len(v.denom.terms())==1 and not any(v.numer.terms()[0][0][3:]) and not any(v.denom.terms()[0][0][3:])
piv=[];start=time.time()
while R:
 choices=[i for i,(r,l) in enumerate(R) if any(mono_safe(v) for v in r.values())]
 if not choices:break
 ii=min(choices,key=lambda i:len(R[i][0]));row,label=R.pop(ii)
 j=min((j for j,v in row.items() if mono_safe(v)),key=lambda j:sum(j in rr for rr,ll in R))
 val=row[j];row={c:v/val for c,v in row.items()};piv.append((j,row,label))
 new=[]
 for rr,ll in R:
  if j in rr:
   v=rr[j]
   for c,u in row.items():
    rr[c]=rr.get(c,K.zero)-v*u
    if not rr[c]:del rr[c]
  if rr:new.append((rr,ll))
 R=new
 if time.time()-start>45:raise TimeoutError
print('monomial rank',len(piv),'residual rows',len(R),'columns',sorted({j for rr,ll in R for j in rr}),flush=True)
from sympy import groebner,factor,symbols
res=[(label,{j:str(factor(v.as_expr())) for j,v in row.items()}) for row,label in R]
for label,row in res:print(label,row,flush=True)
if all(len(row)==1 for row,label in R):
 polys=[next(iter(row.values())).numer.as_expr() for row,label in R]
 print('GB',groebner(polys,*symbols('a x y z')),flush=True)

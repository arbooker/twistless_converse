"""Exact exclusion of integer poles s>=3 on the enlarged weight-2 grids.
Only applies at the exceptional signs/eigenvalues in level21_22_extra_prime5.tex.
Use the old-grid theorem to set embedded coordinates to zero, and use the
Hecke-5 sum rows, whose eigenvalue terms then vanish. Monomial pivots and
an exponential-polynomial dominance certificate prove full rank for h>=2
integer. This yields unconditional lambda5 constraints if a pole at s=2
exists; it does not eliminate that pole or prove modularity.
"""
import sys,time
from pathlib import Path
N=int(sys.argv[1]);source=Path(__file__).with_name('level21_22_extra_prime5.py').read_text();source=source[:source.index('KK,t=field')];exec(source)
from sympy import factor
rows=[]
for row,l in original:
 rr={j:K(v.as_expr().subs({aa:point[aa]})) for j,v in row.items()};rr={j:v for j,v in rr.items() if v}
 if rr: rows.append((rr,l))
for j in range(oldQ):rows.append(({5*j:K.one},('old',j)))
for j in range(Q//5):rows.append(({j+k*(Q//5):K.one for k in range(5)},('H5',j)))
R=rows;basis=[];st=time.time()
def safe(v):return len(v.numer.terms())==len(v.denom.terms())==1
while R:
 choices=[i for i,(r,l) in enumerate(R) if any(safe(v) for v in r.values())]
 if not choices:break
 ii=min(choices,key=lambda i:len(R[i][0]));row,lab=R.pop(ii)
 j=min((j for j,v in row.items() if safe(v)),key=lambda j:sum(j in rr for rr,ll in R))
 val=row[j];row={i:v/val for i,v in row.items()};basis.append((j,row,lab));new=[]
 for rr,ll in R:
  if j in rr:
   c=rr[j]
   for i,v in row.items():
    rr[i]=rr.get(i,K.zero)-c*v
    if not rr[i]:del rr[i]
  if rr:new.append((rr,ll))
 R=new
 if time.time()-st>50:raise TimeoutError
print('N',N,'monomial rank',len(basis),'residualcols',sorted({j for row,l in R for j in row}),'rows',len(R),'seconds',time.time()-st,flush=True)

from sympy import Poly,symbols
cols=sorted({j for row,l in R for j in row});assert len(cols)==2
success=None
for i in range(min(12,len(R))):
 for j in range(i):
  det=R[i][0].get(cols[0],K.zero)*R[j][0].get(cols[1],K.zero)-R[i][0].get(cols[1],K.zero)*R[j][0].get(cols[0],K.zero)
  if not det:continue
  num=det.numer.as_expr()
  if num.free_symbols - {xx,yy}:continue
  terms={2**ij[0]*3**ij[1]:int(c) for ij,c in Poly(num,xx,yy).terms()}
  top=max(terms);lead=abs(terms[top]);other={b:c for b,c in terms.items() if b!=top}
  cutoff=next((n for n in range(2,51) if sum(abs(c)*b**n for b,c in other.items())<lead*top**n),None)
  if cutoff is None:continue
  values=[sum(c*b**n for b,c in terms.items()) for n in range(2,cutoff)]
  if any(v==0 for v in values):continue
  success=(R[i][1],R[j][1],det,cutoff,terms,values);break
 if success:break
assert success
print('POSITIVE_INTEGER_CERTIFICATE',N,success[:2],'det',factor(success[2].as_expr()),'cutoff',success[3],'terms',success[4],'smallvalues',success[5],flush=True)

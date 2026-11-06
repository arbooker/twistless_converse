"""Exact three-row first-jet identity for N=19 and lambda_2=0.
Uses SymPy only. Run from the project root.
"""
from pathlib import Path
import sys
sys.argv=[sys.argv[0],sys.argv[1] if len(sys.argv)>1 else '-1',sys.argv[2] if len(sys.argv)>2 else '-1','zero2']
source=Path(__file__).with_name('level19_pole_probe.py').read_text()
base=source[source.index('import sys,time'):source.index('pivs,jrows=elim(jet,Q)')]
base=base.replace('piv.append(j)','piv.append((j,dict(rr)))')
exec(base)
opivs,orows=elim([(dict(r),l) for r,l in original],Q)
jpivs,jrows=elim(jet,Q)
for rr,ll in jrows:
 for j,pr in opivs:
  val=rr.get(Q+j,K.zero)
  if val:
   for cc,vv in pr.items():
    cc+=Q;rr[cc]=rr.get(cc,K.zero)-val*vv
    if not rr[cc]:del rr[cc]
jrows=[(r,l) for r,l in jrows if r]
assert eta==-1 and bad in [-1,1]
assert len(jrows)==(80 if bad==-1 else 76)
i,j=(59,66) if bad==-1 else (55,62)
co={i:K.one,j:-(x*x+4)/(x*x),17:3*b/y}
sy={}
for i,c in co.items():
 for j,v in jrows[i][0].items():sy[j]=sy.get(j,K.zero)+c*v
assert all(not v for j,v in sy.items() if j<Q)
vv=[1-x*x,K.zero,y*y+1]
scalar=sum((sy.get(j,K.zero)*v for j,v in zip([132,156,198],vv)),K.zero)
P=3*x**6+12*x**4+x*x*y*y-18*x*x-4*y*y
assert scalar==-361*P/(6*x*x*y*y)
print('Verified three-row syzygy with only monomial denominators.')
print('Necessary scalar:',P)

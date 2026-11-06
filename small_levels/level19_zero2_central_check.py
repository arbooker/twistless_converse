"""Exact leading-row check for N=19, lambda_2=0, central gap n=0.
Run from the project root; SymPy only.
"""
import sys
sys.argv=[sys.argv[0],sys.argv[1] if len(sys.argv)>1 else "-1",sys.argv[2] if len(sys.argv)>2 else "-1","zero2"]
from pathlib import Path
import sys,sympy as sp
src=Path('small_levels/level19_pole_probe.py').read_text();exec(src[src.index('import sys,time'):src.index('pivs,jrows=elim(jet,Q)')])
pivs,rem=elim(original,Q)
xx,yy,zz,aa,bb=sp.symbols('x y z a b')
rows=[]
for rr,ll in rem:
 row=[sp.factor(rr.get(j,K.zero).as_expr().subs({xx:sp.I,aa:0})) for j in [18,42,84]]
 if any(row):rows.append((row,ll))
Y,B,Z,T=sp.symbols('Y B Z T');rs=[]
for row,l in rows:
 rr=[]
 for e in row:
  e=sp.Poly(sp.expand(e*2*yy**8),yy,bb,zz);dd={}
  for (iy,ib,iz),c in e.terms():
   assert (iy-ib)%2==0 and iy>=ib
   dd[((iy-ib)//2,ib,iz)]=c
  rr.append(sp.Poly.from_dict(dd,(Y,B,Z)).as_expr())
 rs.append((rr,l))
# substitute w=(u-v)/(Y+1)
ss=[[sp.expand(2*r[0]+(Y+1)*r[1]),sp.expand(2*r[0]+(Y+1)*r[2])] for r,l in rs]
ps=[]
for i,r in enumerate(ss):
 for s in ss[i+1:]:
  p=sp.factor(r[0]*s[1]-r[1]*s[0])
  if p:
   pp=sp.Poly(p,Y,B,Z).monic().as_expr()
   if pp not in ps:ps.append(pp)
print('DETS',len(ps),flush=True)
gb=sp.groebner(ps+[T*Y*(Y+1)-1],B,Z,T,Y,order='grevlex');print('GB',list(gb),flush=True)

print("LEX",list(gb.fglm(order="lex")),flush=True)

p=Y**3-Y**2+Y-1
assert gb.reduce(p)[1]==0
assert sp.rem(Y**4-1,p,Y)==0
print("Verified: Y must be a fourth root of unity.")

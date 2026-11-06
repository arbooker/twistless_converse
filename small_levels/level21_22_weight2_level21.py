"""Exact elimination of the exceptional N21 simple weight-two pole.

Analytic dependencies: level21_poles.tex, level21_22_weight2_chi5.tex,
and the established closed-Taylor continuation lemma.
This verifies all new transformation identities and both grid ranks.
It does not assert full Gamma0(21) generation.
"""
import sys,time,json,hashlib
from pathlib import Path
import sympy as sp
base=Path(__file__).parent
T=sp.Matrix([[1,1],[0,1]]);U=sp.Matrix([[1,0],[21,1]])
E=sp.Matrix([[2,-1],[-21,11]])
A=sp.Matrix([[5,1],[-21,-4]]);B=sp.Matrix([[5,-1],[21,-4]])
C=sp.Matrix([[5,-2],[-42,17]]);D=sp.Matrix([[5,2],[42,17]])
t=lambda q:sp.Matrix([[1,q],[0,1]])
assert C==E*T*D.inv()*U*E
elliptic=C.inv()*E*t(sp.Rational(1,5))
assert elliptic==sp.Matrix([[-8,sp.Rational(17,5)],[-21,sp.Rational(44,5)]])
assert elliptic.det()==1 and elliptic.trace()==sp.Rational(4,5)
M0=sp.Matrix([[2,0],[0,1]]);M1=sp.Matrix([[1,0],[0,2]]);M2=sp.Matrix([[1,1],[0,2]])
assert M0*A==-T.inv()*E.inv()*M1
assert M1*A==C*M2
assert M2*A==E.inv()*U.inv()*D*M0
print('N21_NEW_TRANSFORMATION_IDENTITIES_PASS',flush=True)
source=(base/'level21_augmented_builder.py').read_text()
source=source.replace('N=21;Q=42','N=21;Q=126').replace('return old','return old | {((5,1,-21,-4),1),((5,-1,21,-4),1),((5,-2,-42,17),1),((5,2,42,17),1)}').replace('if zero2:a=K.zero','a=-K(3)/2')
sys.argv=['certificate','-1','-1','1'];exec(source)
original=[(dict(row),lab) for row,lab in R]
# Exact finite-field rank is a nonzero rational-minor certificate, since
# each specialized denominator is explicitly checked to remain nonzero.
prime=1000003;point={sp.Symbol('x'):2,sp.Symbol('y'):3,sp.Symbol('z'):7};numeric=[]
for row,lab in original:
 rr={}
 for j,v in row.items():
  num,den=v.as_expr().subs(point).as_numer_denom()
  assert not num.free_symbols and not den.free_symbols
  assert int(den)%prime
  w=int(num)*pow(int(den),-1,prime)%prime
  if w:rr[j]=w
 numeric.append(rr)
nb={}
for rr in numeric:
 while rr:
  j=min(rr)
  if j not in nb:
   iv=pow(rr[j],-1,prime);nb[j]={i:v*iv%prime for i,v in rr.items()};break
  c=rr[j]
  for i,v in nb[j].items():
   value=(rr.get(i,0)-c*v)%prime
   if value:rr[i]=value
   else:rr.pop(i,None)
assert len(nb)==126
print('N21_Q126_H1_FULL_RANK',len(nb),flush=True)
# At a pole where all old-grid coordinates vanish, add their unit rows.
# Monomial pivots below never vanish at any complex s.
R=[(dict(row),lab) for row,lab in original]
for j in range(42):R.append(({3*j:K.one},('old',j)))
piv=[];st=time.time()
def safe(v):return len(v.numer.terms())==len(v.denom.terms())==1
while R:
 choices=[i for i,(r,l) in enumerate(R) if any(safe(v) for v in r.values())]
 assert choices,('no monomial pivot',len(piv))
 ii=min(choices,key=lambda i:len(R[i][0]));row,lab=R.pop(ii)
 j=min((j for j,v in row.items() if safe(v)),key=lambda j:sum(j in rr for rr,ll in R))
 val=row[j];assert safe(val);row={i:v/val for i,v in row.items()};piv.append((j,str(val),lab));new=[]
 for rr,ll in R:
  if j in rr:
   c=rr[j]
   for i,v in row.items():
    rr[i]=rr.get(i,K.zero)-c*v
    if not rr[i]:del rr[i]
  if rr:new.append((rr,ll))
 R=new
assert len(piv)==126
print('N21_Q126_OLD_ZERO_UNIFORM_RANK',len(piv),'seconds',time.time()-st,flush=True)
files=['level21_22_weight2_level21.py','level21_22_weight2_chi5.py','level21_augmented_builder.py']
manifest={'theorem':'N21 original Q42 twists are entire also in the exceptional k2 case; new Q126 twists then entire','new_elliptic_trace':'4/5','h1_finite_field':prime,'h1_rank':len(nb),'old_zero_uniform_rank':len(piv),'sha256':{f:hashlib.sha256((base/f).read_bytes()).hexdigest() for f in files}}
(base/'level21_22_weight2_level21.json').write_text(json.dumps(manifest,indent=2)+'\n')

"""Exact rank removing the final exceptional N22 weight-two pole.

Adds the two cross-Fricke equations obtained from the entire chi5 twist
and the Ramanujan-5 twist. The existing old-grid pole and extra-prime5
certificates justify the eigenvalue specialization and absence of higher
integer pole sources. See the companion .tex for the full implication.
"""
import sys,json,hashlib
from pathlib import Path
import sympy as sp
base=Path(__file__).parent
sys.argv=['certificate','22']
source=(base/'level21_22_extra_prime5.py').read_text();source=source[:source.index('KK,t=field')]
exec(source)
assert N==22 and Q==330
# Exact Hecke-5 relation at the value forced by an original-grid pole.
for j in range(Q//5):
 rr={j+k*(Q//5):K.one for k in range(5)}
 for col,v in [(5*j%Q,K(19)/(5*b)),(25*j%Q,b**-2)]:rr[col]=rr.get(col,K.zero)+v
 add(rr,('H',5,j))
# Entire S1 and S2 are exchanged under the same Fricke at conductor550.
for src_pair,target_pair in [(1,2),(2,1)]:
 q=5;ell=lcm(N,q*q);d=Q*Q//ell
 assert ell==550 and d==198
 add({src_pair*Q//5:K.one,(-src_pair*Q//5)%Q:K.one},('splitR',src_pair))
 for tt in divisors(d):
  for t0 in [tt,-tt]:
   u=-d//t0;c=-eta*mon(Fraction(ell*t0*t0,Q*Q));rr={}
   for a0 in [src_pair,-src_pair]:
    j=(a0*Q//5+t0)%Q;rr[j]=rr.get(j,K.zero)+1
   for a0 in [target_pair,-target_pair]:
    j=(a0*Q//5+u)%Q;rr[j]=rr.get(j,K.zero)+c
   add(rr,('splitF',src_pair,target_pair,t0))
prime=1000003;basis={}
for row,lab in R:
 rr={}
 for j,v in row.items():
  num,den=v.as_expr().subs(point).as_numer_denom()
  assert not num.free_symbols and not den.free_symbols
  assert int(den)%prime
  w=int(num)*pow(int(den),-1,prime)%prime
  if w:rr[j]=w
 while rr:
  j=min(rr)
  if j not in basis:
   iv=pow(rr[j],-1,prime);basis[j]={i:v*iv%prime for i,v in rr.items()};break
  c=rr[j]
  for i,v in basis[j].items():
   value=(rr.get(i,0)-c*v)%prime
   if value:rr[i]=value
   else:rr.pop(i,None)
assert len(basis)==330
print('N22_Q330_SPLIT_CHI5_H1_FULL_RANK',len(basis),flush=True)
print('N22_EXCEPTIONAL_WEIGHT_TWO_POLE_EXCLUDED',flush=True)
files=['level21_22_weight2_level22.py','level21_22_weight2_chi5_22.py','level21_22_extra_prime5.py','level22_uniform_continuation.py']
manifest={'theorem':'All original Q66 additive twists are entire at N22, including the sole exceptional weight2 case','rank':330,'finite_field':prime,'parameters':{'eta':-1,'sigma2':-1,'sigma11':1,'lambda3':'-7/3','lambda5':'-19/5'},'sha256':{f:hashlib.sha256((base/f).read_bytes()).hexdigest() for f in files}}
(base/'level21_22_weight2_level22.json').write_text(json.dumps(manifest,indent=2)+'\n')

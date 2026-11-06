"""Exact N25 eta-plus highest q5 pole-sector exclusion certificate.
This is NOT a full converse or a proof that every additive twist is holomorphic.
"""
import sys,json,hashlib
from pathlib import Path
base=Path(__file__).parent
sys.argv=[sys.argv[0],'1']
exec((base/'level25_finish_plus_germ.py').read_text())
assert all(all(poles[t][j]==0 for t in range(3)) for j in [30,60,90,120])
assert poles[3][120]==1
for target in [a*x+x*x+2,b*y+y*y+3]:
 assert any(set(row)=={120} and safe(row[120]/target) for row,rid in R)
import sympy as sp
XX,YY,ZZ,UU=sp.symbols('X Y Z U')
G=9*XX**2-4*YY**2
p1=25*G*(XX**2-4);p2=25*G*(YY**2-9)
assert any(sp.expand(p-p1)==0 for p in minors)
assert any(sp.expand(p-p2)==0 for p in minors)
assert sp.expand(9*p1-4*p2-25*G**2)==0
print('PLUS_GERM_FORCES_CIRCLE_PASS',flush=True)
exec((base/'level25_finish_plus_higherjet.py').read_text())
assert n==2 and len(basis)==4
assert any(lab==('H',2,20) and bb== -125*(9*X*X-104)/(4*X*X) for lab,bb in bad)
circle_gcd=[]
for ii,d in enumerate(determinants):
 for pol in [d.numer,d.denom]:
  ex=pol.as_expr();assert not ex.has(ZZ)
  pu=sp.Poly(ex,XX);assert all(pw[0]%2==0 for pw,co in pu.terms())
  poly=sum(co*UU**(pw[0]//2) for pw,co in pu.terms())
  rev=sp.expand(UU**sp.degree(poly,UU)*poly.subs(UU,16/UU))
  cg=sp.Poly(sp.gcd(poly,rev),UU).monic().as_expr()
  # Denominators are monomials, and the only circle zero is U=4
  # in the numerator of the first lower-point minor.
  if pol==d.numer:
   assert cg==([1,UU-4,1][ii]),(ii,cg)
   circle_gcd.append(str(cg))
  else:assert len(pol.terms())==1
print('PLUS_CIRCLE_RANKS_AND_SECOND_JET_PASS',flush=True)
exec((base/'level25_finish_plus_exceptional.py').read_text(),{'__file__':str(base/'level25_finish_plus_exceptional.py'),'__name__':'__main__'})
files=['level25_finish_eta_plus_cusp_poles.py','level25_finish_plus_germ.py',
 'level25_finish_plus_higherjet.py','level25_finish_plus_exceptional.py',
 'level25_finish_firstjet.py','level25_finish_augmented.py','level25_uniform_continuation.py']
manifest={'statement':'N25 eta=+1: every rightmost non-weight pole, or weight-point pole of maximum grid order at least two, has zero denominator-five highest coefficient',
 'scope':'Excludes one highest-order pole sector; denominator25 modes, simple cusp constants, and full converse remain open',
 'germ_relation':'9*x^2=4*y^2',
 'circle_minor_gcds':circle_gcd,
 'second_jet_obstruction':'-125*(9*x^2-104)/(4*x^2)',
 'exceptional_branch':'h=1,lambda2=-3,lambda3=-4',
 'exceptional_three_level_rank':450,
 'source_sha256':{name:hashlib.sha256((base/name).read_bytes()).hexdigest() for name in files}}
(base/'level25_finish_eta_plus_cusp_poles.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('N25_ETA_PLUS_NONWEIGHT_CUSP_POLE_EXCLUSION_PASS',flush=True)

"""Certificate for the N25 eta=-1 non-weight, rightmost cusp-pole lemma.

This is deliberately NOT a converse-theorem certificate. It addresses
highest-order pole vectors with a nonzero denominator-five component.
"""
import sys,json,hashlib
from pathlib import Path
base=Path(__file__).parent
sys.argv=[sys.argv[0],'-1']
source=(base/'level25_finish_firstjet.py').read_text()
exec(source[:source.index('from sympy import factor')])
assert free==[42,60,108,120,126]
assert len(cp)==1 and cp[0][0]==1 and cp[0][1]=={1:K.one,3:K(1)/2}
assert [pole[30] for pole in poles]==[K.zero,K.zero,K.zero,-K.one,K.zero]
assert [pole[60] for pole in poles]==[K.zero,K.one,K.zero,K.zero,K.zero]
assert [pole[90] for pole in poles]==[K.zero,-K.one,K.zero,K.zero,K.zero]
assert [pole[120] for pole in poles]==[K.zero,K.zero,K.zero,K.one,K.zero]
F1=2*a*x+x*x-2
F2=-9*a*x+18*x*x-10*y*y+9
F3=-3*a*x+6*b*y+6*x*x+2*y*y-3
for f in [F1,F2,F3]:
 assert any(set(row)=={3} and safe(row[3]/f) for row,lab in R)
assert 2*F2+9*F1==5*(9*x*x-4*y*y)
assert 3*F3-F2==2*(9*b*y+8*y*y-9)
print('FORCED_BRANCH_IDENTITIES_PASS',flush=True)
exec((base/'level25_finish_nonweight_branch.py').read_text())
import sympy as sp
XX,ZZ,UU=sp.symbols('X Z U')
assert g is not None and not g.has(ZZ)
pol=sp.Poly(g,XX)
assert all(pw[0]%2==0 for pw,co in pol.terms())
P=sum(co*UU**(pw[0]//2) for pw,co in pol.terms())
d=sp.degree(P,UU)
circle=sp.Poly(sp.gcd(P,sp.expand(UU**d*P.subs(UU,16/UU))),UU).monic().as_expr()
assert circle==UU-4,circle
print('CIRCLE_GCD_PASS',circle,flush=True)
coeff_minor=det.numer.as_expr()
assert not coeff_minor.has(ZZ)
polyD=sp.Poly(coeff_minor,XX)
assert all(pw[0]%2==0 for pw,co in polyD.terms())
Dpoly=sum(co*UU**(pw[0]//2) for pw,co in polyD.terms())
dd=sp.degree(Dpoly,UU)
dcircle=sp.Poly(sp.gcd(Dpoly,sp.expand(UU**dd*Dpoly.subs(UU,16/UU))),UU).monic().as_expr()
assert dcircle==1,dcircle
print('LOWER_POINT_FULL_RANK_ON_CIRCLE_PASS',flush=True)
files=['level25_finish_eta_minus_cusp_poles.py','level25_finish_firstjet.py',
       'level25_finish_nonweight_branch.py','level25_finish_augmented.py',
       'level25_uniform_continuation.py','level25_finish_minus_higherjet.py']
manifest={'statement':'N25 eta=-1: every rightmost non-weight pole, or weight-point pole of maximum grid order at least two, has zero denominator-five highest coefficient',
 'scope':'Excludes one highest-order pole sector; weight point, denominator25 modes and full converse open',
 'leading_rank':145,'first_jet_cusp_relation':'r60=-r120/2',
 'forced_relation':'9*x^2=4*y^2','minor_gcd':str(sp.factor(g)),
 'circle_gcd':str(circle),
 'coefficient_minor':str(sp.factor(coeff_minor)),
 'coefficient_circle_gcd':str(dcircle),
 'source_sha256':{name:hashlib.sha256((base/name).read_bytes()).hexdigest() for name in files}}
exec((base/'level25_finish_minus_higherjet.py').read_text(),{'__file__':str(base/'level25_finish_minus_higherjet.py'),'__name__':'__main__'})
manifest['third_jet_obstruction']='R5: -25/2, ranks 150 at shifts 0,1,2,3'
(base/'level25_finish_eta_minus_cusp_poles.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('N25_ETA_MINUS_NONWEIGHT_CUSP_POLE_EXCLUSION_PASS',flush=True)

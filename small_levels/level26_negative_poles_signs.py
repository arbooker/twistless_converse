"""Exact reduction of all four negative bad-13 loci to the audited MMM locus."""
from pathlib import Path
import hashlib
import json
import sympy as s

base=Path(__file__).parent
x=s.symbols('x')
data={c:json.loads((base/('level26_negative_poles_'+c+'_projection.json')).read_text())
      for c in ['mmm','mpm','pmm','ppm']}
p0=s.Poly(s.sympify(data['mmm']['x_polynomial']),x,domain=s.QQ)
y0=s.Poly(s.sympify(data['mmm']['Y_polynomial']),x,domain=s.QQ)
results={}
for code,eps,extra in [('mmm',1,1),('mpm',-1,x*x+5*x+8),
                        ('pmm',1,x*x-5*x+8),('ppm',-1,1)]:
    p=s.Poly(s.sympify(data[code]['x_polynomial']),x,domain=s.QQ)
    y=s.Poly(s.sympify(data[code]['Y_polynomial']),x,domain=s.QQ)
    pp=s.Poly(eps*p0.as_expr().subs(x,eps*x),x)
    yy=s.Poly(y0.as_expr().subs(x,eps*x),x)
    assert p==pp*s.Poly(extra,x)
    assert (y-yy).rem(pp).is_zero
    if extra!=1:
        q=s.Poly(extra,x)
        assert y.rem(q).as_expr()==9
        assert s.discriminant(q.as_expr(),x)==-7
        assert q.TC()==8
    results[code]={'x_reflection':eps,'extra_factor':str(extra),
                  'Y_congruence':'Y_case(x)=Y_mmm(eps*x) modulo reflected degree21 polynomial',
                  'extra_branch':'none' if extra==1 else 'nonreal conjugate x roots have |x|^2=8, while Y=9; physical real part h would be both 3/2 and 1'}
audit_path=base/'level26_root_modulus_mmm.json'
audit=json.loads(audit_path.read_text())
projection=base/'level26_negative_poles_mmm_projection.json'
assert audit['projection_sha256']==hashlib.sha256(projection.read_bytes()).hexdigest()
assert len(audit['root_disks'])==p0.degree()==21
manifest={'claim':'All four negative-bad13 finite projection loci are physically impossible, using the independent MMM rational-disk audit.',
          'cases':results,'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
           for p in [Path(__file__),audit_path]+[base/('level26_negative_poles_'+c+'_projection.json') for c in data]}}
(base/'level26_negative_poles_signs.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('N26_ALL_FOUR_NEGATIVE_PROJECTIONS_EXCLUDED_EXACTLY')

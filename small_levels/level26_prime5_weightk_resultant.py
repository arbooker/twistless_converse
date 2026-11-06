"""Specialization-safe simple weight-k obstruction from Q780 leading rows.

Preparation: run level26_prime5_weightk_eliminate.py CODE magma to export
the five normalized leading chart polynomials. This script makes only
polynomial resultants and divisions by powers of the nonzero x variable.
Magma has one thread, a 500MB memory limit, and a 45 second alarm.
"""
from pathlib import Path
import json, re, sys
import sympy as S

code = sys.argv[1] if len(sys.argv) > 1 else 'mmm'
A,t,B,z,W,x,Y = S.symbols('A t B z W x Y')
p = list(map(S.sympify, json.loads(Path('/tmp/level26_prime5_weightk_polys_'+code+'.json').read_text())))
assert len(p) == 5
bc = S.diff(p[4],B)
assert bc in [x*x,-x*x]
assert not p[0].has(B) and not p[1].has(B)
# p4-p0=0 gives B=-bn/bc, where bc=±x². Substitution into x²*p3 clears
# all denominators. Its common zero with p0,p1 is necessary.
bn = S.expand(p[4]-p[0]-B*bc)
q = S.Poly(S.cancel((x*x*p[3]).subs(B,-bn/bc)), A,t,z,W,x,Y).as_expr()
r = S.Poly(S.resultant(p[0],p[1],t),A,z,W,x,Y)
v = S.Poly(S.resultant(p[0],q,t),A,z,W,x,Y)
def strip_x(poly):
    power = min(exps[-2] for exps,c in poly.terms())
    return S.cancel(poly.as_expr()/x**power),power
r,rpower = strip_x(r)
v,vpower = strip_x(v)
# In the other projective chart, the t coefficients of p0,p1
# already give two necessary equations independent of B.
u0 = S.Poly(p[0],t).coeff_monomial(t)
u1 = S.Poly(p[1],t).coeff_monomial(t)
assert not u0.has(B) and not u1.has(B)
zero = S.resultant(u0,u1,A)
fmt = lambda e: str(e).replace('**','^')
stem='/tmp/level26_prime5_weightk_resultant_'+code
script = ('SetNthreads(1);SetMemoryLimit(500000000);Alarm(45);\n'
 'R<A,x,Y,z,W>:=PolynomialRing(Rationals(),5);\n'
 'r:='+fmt(r)+';\nv:='+fmt(v)+';\n'
 'time d:=Resultant(r,v,A);\n'
 'PrintFile("'+stem+'.txt",d : Overwrite:=true);\n'
 'print "resultant computed", #Monomials(d);quit;\n')
Path(stem+'.m').write_text(script)
if 'prepare' in sys.argv:
    print(stem+'.m',flush=True)
    sys.exit(0)

def parse_terms(s):
    """Parse expanded Magma integer polynomial without costly symbolic sums."""
    out=[]
    for a in re.findall(r'[+-]?[^+-]+',re.sub(r'\s+','',s)):
        coeff=-1 if a.startswith('-') else 1
        exps=dict.fromkeys(['x','Y','z','W'],0)
        for f in a.lstrip('+-').split('*'):
            if f.isdigit(): coeff*=int(f)
            else:
                var,*power=f.split('^')
                exps[var]+=int(power[0]) if power else 1
        out.append([list(exps.values()),coeff])
    return out

def abel_certificate(terms):
    seq=sorted([(2**e[0]*9**e[1]*13**e[2]*25**e[3],c) for e,c in terms],reverse=True)
    assert len({b for b,c in seq})==len(seq)
    sign=1 if seq[0][1]>0 else -1
    for m in range(1,41):
        tail=0; good=True
        for base,c in seq:
            tail+=sign*c*base**m
            if tail<0: good=False;break
        if good and tail>0: break
    else: raise AssertionError('No Abel threshold at most40')
    values=[sum(c*base**j for base,c in seq) for j in range(1,m)]
    return dict(threshold=m,orientation=sign,finite_values=values,
                finite_zero_weights=[2*(j+1) for j,v in enumerate(values) if v==0])

terms=parse_terms(Path(stem+'.txt').read_text())
zterms=[[list(e),int(c)] for e,c in S.Poly(zero,x,Y,z,W).terms()]
data=dict(code=code,original_polynomials=list(map(str,p)),
          first_resultant=str(r),second_resultant=str(v),
          stripped_x_powers=[rpower,vpower],resultant_terms=terms,
          nonzero_chart=abel_certificate(terms),
          zero_chart_terms=zterms,zero_chart=abel_certificate(zterms))
Path(stem+'.json').write_text(json.dumps(data,indent=2))
print(code,{key:{k:v for k,v in data[key].items() if k!='finite_values'} for key in ['nonzero_chart','zero_chart']},flush=True)

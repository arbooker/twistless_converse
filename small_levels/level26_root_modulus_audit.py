"""Exact rational disks exclude the physical modulus relation on a finite locus.

Numerical roots only choose disk centers. Rational Rouche inequalities prove
that the disjoint disks contain every root, then rational power comparisons
exclude |Y|=|x|**(log(9)/log(2)). No numerical inequality is trusted.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb
import hashlib
import json
import signal
import sys
import sympy as S

signal.alarm(120)
root = Path(__file__).resolve().parent
code = sys.argv[1] if len(sys.argv)>1 else 'mmm'
source = root / ('level26_negative_poles_'+code+'_projection.json')
data = json.loads(source.read_text())
x = S.Symbol('x')
p = S.Poly(S.sympify(data['x_polynomial']), x)
q = S.Poly(S.sympify(data['Y_polynomial']), x)
def rat(v):
    return F(int(S.numer(v)), int(S.denom(v)))
def add(a,b): return (a[0]+b[0], a[1]+b[1])
def mul(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def norm1(a): return abs(a[0])+abs(a[1])
def norm2(a): return a[0]**2+a[1]**2
def shift(poly,c):
    out=[]
    for a in poly.all_coeffs():
        nxt=[(F(0),F(0)) for _ in range(len(out)+1)]
        for j,v in enumerate(out):
            nxt[j]=add(nxt[j],mul(c,v));nxt[j+1]=add(nxt[j+1],v)
        nxt[0]=add(nxt[0],(rat(a),F(0)))
        out=nxt
    return out
radius=F(1,10**40)
scale=10**12
def down(v):return F((v*scale).__floor__(),scale)
def up(v):return F((v*scale).__ceil__(),scale)
def modulus_square_bounds(center,error):
    n=norm2(center);delta=2*norm1(center)*error+error**2
    lo,hi=down(n-delta),up(n+delta)
    assert 0<lo<=hi
    return lo,hi

# This exact integer inequality bounds rho=log(9)/log(2).
assert 2**3169 < 9**1000 < 2**3170
centers=[(F(str(S.re(v))),F(str(S.im(v)))) for v in p.nroots(n=80,maxsteps=1000)]
assert len(centers)==p.degree()
for i,c in enumerate(centers):
    for d in centers[:i]: assert norm2((c[0]-d[0],c[1]-d[1])) > 4*radius**2
cert=[]
for i,c in enumerate(centers):
    pc=shift(p,c)
    upper=norm1(pc[0])+sum(norm1(v)*radius**j for j,v in enumerate(pc) if j>=2)
    lower=max(abs(pc[1][0]),abs(pc[1][1]))*radius
    assert upper<lower, (i,'Rouche failed')
    qc=shift(q,c)
    err=sum(norm1(v)*radius**j for j,v in enumerate(qc) if j>=1)
    xl,xu=modulus_square_bounds(c,radius)
    yl,yu=modulus_square_bounds(qc[0],err)
    assert xu<1 or xl>1, (i,'disk crosses modulus one')
    # Squared moduli obey the same exponent rho.
    if xl>1:
        below = yu**1000 < xl**3169
        above = yl**1000 > xu**3170
    else:
        below = yu**1000 < xl**3170
        above = yl**1000 > xu**3169
    assert below or above, (i,'physical modulus not excluded',float(xl),float(yl))
    cert.append({'center':[str(v) for v in c], 'radius':str(radius),
                 'x_squared_modulus':[str(xl),str(xu)],
                 'Y_squared_modulus':[str(yl),str(yu)],
                 'side':'below' if below else 'above'})
    print(code,'root disk',i+1,'Rouche and physical-modulus exclusion PASS',flush=True)
out={'claim':'Every root of x_polynomial with Y=Y_polynomial(x) violates |Y|=|x|^(log9/log2).',
     'projection_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
     'auditor_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'exponent_bounds':['3169/1000','3170/1000'], 'root_disks':cert}
(root/('level26_root_modulus_'+code+'.json')).write_text(json.dumps(out,indent=2)+'\n')
print('ALL_ROOTS_EXCLUDED',code,len(cert),flush=True)

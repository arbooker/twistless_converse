"""Exact rational disk proof for P(X)=0, Y=H(X), X=4^h, Y=9^h.

PARI approximations select centers only. Every proof inequality below is
rational, including outward rounding during polynomial evaluation.
Scratch files and completion markers are outside the shared project.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import signal
import sys

signal.alarm(120)
ROOT = Path(__file__).resolve().parent
SOURCE = ROOT/'level25_plus_poles_chart1_shape.json'
CENTERS = Path('/tmp/level25_root_chart1_centers.txt')
DATA = json.loads(SOURCE.read_text())
P, H = [[F(a) for a in DATA[k]] for k in ('P', 'H')]

def derivative(p):
    return [i*a for i,a in enumerate(p)][1:]

if len(sys.argv) > 1 and sys.argv[1] == 'prepare':
    poly = '+'.join('(%s)*X^%d' % (a,i) for i,a in enumerate(P))
    # A new center file is used for this invocation; old proof results are not read.
    gp = '\n'.join([
        'default(parisizemax,500000000);', 'default(realprecision,450);',
        'p='+poly+';', 'v=polroots(p);',
        'for(i=1,#v,write("'+str(CENTERS)+'",real(v[i]));write("'+str(CENTERS)+'",imag(v[i])));',
        'write("/tmp/level25_root_chart1_centers.pass","PASS 67 centers");', 'quit;'])
    assert not CENTERS.exists(), 'Choose a fresh center filename for a new run'
    Path('/tmp/level25_root_chart1_centers.gp').write_text(gp+'\n')
    print('Prepared bounded-precision PARI center discovery; no proof claimed.')
    sys.exit(0)

SCALE = 10**450
RADIUS = F(1,10**250)
OUT_SCALE = 10**18

def up_to(v, scale):
    return F(-((-v*scale).__floor__()),scale)

def down_to(v, scale):
    return F((v*scale).__floor__(),scale)

def norm1(c):
    return abs(c[0])+abs(c[1])

def norm2(c):
    return c[0]**2+c[1]**2

def evaluate(p,c):
    """Return center and L1 error, with exact outward rounded Horner steps."""
    v = (F(0),F(0))
    error = F(0)
    for a in reversed(p):
        z = (c[0]*v[0]-c[1]*v[1]+a,c[0]*v[1]+c[1]*v[0])
        w = (down_to(z[0],SCALE),down_to(z[1],SCALE))
        error = up_to(norm1(c)*error+abs(z[0]-w[0])+abs(z[1]-w[1]),SCALE)
        v = w
    return v,error

def absolute_bound(p,r):
    v = F(0)
    for a in reversed(p):
        v = up_to(v*r+abs(a),SCALE)
    return v

def squared_bounds(c,e):
    delta = 2*norm1(c)*e+e*e
    return down_to(norm2(c)-delta,OUT_SCALE),up_to(norm2(c)+delta,OUT_SCALE)

saved = ROOT/'level25_root_chart1_modulus_certificate.json'
if saved.exists():
    # Stored centers are merely proposed rational numbers, never trusted results.
    centers = [tuple(F(a) for a in d['center']) for d in json.loads(saved.read_text())['root_disks']]
else:
    centers_text = CENTERS.read_text().splitlines()
    assert len(centers_text) == 2*(len(P)-1)
    centers = [(F(centers_text[i]),F(centers_text[i+1])) for i in range(0,len(centers_text),2)]
assert len(centers) == len(P)-1
for i,c in enumerate(centers):
    for d in centers[:i]:
        assert norm2((c[0]-d[0],c[1]-d[1])) > 4*RADIUS**2

# 1584/1000 < log(9)/log(4) < 1585/1000.
assert 4**1584 < 9**1000 < 4**1585
dp,ddp,dh = derivative(P),derivative(derivative(P)),derivative(H)
cert = []
failed = []
for i,c in enumerate(centers):
    pc,pe = evaluate(P,c)
    dc,de = evaluate(dp,c)
    bound_r = norm1(c)+RADIUS
    remainder = RADIUS**2*absolute_bound(ddp,bound_r)/2
    lhs = norm1(pc)+pe+remainder
    rhs = (max(abs(dc[0]),abs(dc[1]))-de)*RADIUS
    assert lhs < rhs, (i,'Rouche',float(lhs),float(rhs))
    hc,he = evaluate(H,c)
    he += RADIUS*absolute_bound(dh,bound_r)
    xl,xu = squared_bounds(c,RADIUS)
    yl,yu = squared_bounds(hc,he)
    assert 0 < xl <= xu and 0 < yl <= yu, (i,'precision insufficient')
    assert xu < 1 or xl > 1, (i,'modulus-one boundary')
    if xl > 1:
        below,above = yu**1000 < xl**1584, yl**1000 > xu**1585
    else:
        below,above = yu**1000 < xl**1585, yl**1000 > xu**1584
    rec = {'center':[str(v) for v in c], 'radius':str(RADIUS),
           'X_squared_modulus':[str(xl),str(xu)],
           'Y_squared_modulus':[str(yl),str(yu)],
           'side':'below' if below else 'above' if above else 'unresolved'}
    cert.append(rec)
    if not (below or above): failed.append(i)
    print('disk',i+1,'Rouche PASS; modulus',rec['side'],flush=True)
out = {'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
       'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
       'exponent_bounds':['1584/1000','1585/1000'],
       'root_disks':cert,'unresolved_disks':failed,
       'status':'PASS' if not failed else 'PARTIAL'}
Path('/tmp/level25_root_chart1_modulus_result.json').write_text(json.dumps(out,indent=2)+'\n')
assert not failed, failed
(ROOT/'level25_root_chart1_modulus_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
Path('/tmp/level25_root_chart1_modulus.pass').write_text('PASS all67 roots excluded\n')
print('PASS_ALL_ROOTS',len(cert),flush=True)

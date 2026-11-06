"""Exact real-root and exponential-modulus exclusion for the N25 quartic."""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json

def p(x): return 5*x**4+5*x**3-312*x**2-228*x+48
intervals = [('-8.038483','-8.038482'),('-0.900349','-0.900348'),
             ('0.170754','0.170755'),('7.768076','7.768077')]
out=[]
for i,(a,b) in enumerate(intervals):
    a,b=F(a),F(b)
    assert a<b and p(a)*p(b)<0
    if i: assert F(intervals[i-1][1])<a
    # Neither interval, nor its translate by one, crosses zero.
    assert a*b>0 and (a+1)*(b+1)>0
    xl,xu=sorted((abs(a),abs(b)))
    dl,du=sorted((abs(a+1),abs(b+1)))
    if xl>1:
        assert dl**2>xu
        side='below'
    elif xu<1 and dl>1:
        side='below'
    else:
        assert xu<1 and du**2<xl
        side='above'
    out.append({'interval':[str(a),str(b)],'side':side})
assert len(out)==4  # Degree and four distinct sign changes exhaust all roots.
result={'status':'PASS','claim':'For every quartic root X and Y=X^2/(X+1), |Y| differs from |X|^rho for 3/2<rho<2.',
        'polynomial':'5*X^4+5*X^3-312*X^2-228*X+48',
        'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'intervals':out}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS all four quartic roots excluded by exact rational sign intervals')

"""Extract exact two-polynomial Magma projection; never use floating values."""
from pathlib import Path
import hashlib
import json
import sys
import sympy as s

code=sys.argv[1]
assert code in ['mmm','mpm','pmm','ppm']
source=Path(sys.argv[2] if len(sys.argv)>2 else '/tmp/level26_negative_poles_'+code+'_chart1_xy.txt')
x,Y=s.symbols('x Y')
text=source.read_text().replace('\\\n','').replace('^','**').strip()
assert text.startswith('[') and text.endswith(']')
polys=[s.sympify(term) for term in text[1:-1].split(',')]
assert len(polys)==2
rel,pol=polys
assert s.diff(rel,Y)==1 and pol.free_symbols=={x}
yp=s.Poly(Y-rel,x,domain=s.QQ);xp=s.Poly(pol,x,domain=s.QQ)
assert xp.LC()==1 and s.gcd(xp,xp.diff()).degree()==0
dest=Path(__file__).with_name('level26_negative_poles_'+code+'_projection.json')
values={'x_polynomial':str(xp.as_expr()),'Y_polynomial':str(yp.as_expr())}
if dest.exists():
    old=json.loads(dest.read_text())
    assert all(old[k]==v for k,v in values.items())
else:
    values['claim']='Exact necessary finite algebraic locus from primitive polynomial second-order germ syzygies. Chart v0=0 excluded by unit ideal.'
    dest.write_text(json.dumps(values,indent=2)+'\n')
manifest={'case':code,'input_path':str(source),'input_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
          'projection_sha256':hashlib.sha256(dest.read_bytes()).hexdigest(),
          'extractor_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'x_degree':xp.degree(),'Y_degree':yp.degree(),
          'checks':['two exact rational polynomials','relation coefficient of Y is one',
                    'x polynomial monic and squarefree','no floating evaluation']}
dest.with_name('level26_negative_poles_'+code+'_projection_source.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('EXACT_PROJECTION_EXTRACTED',code,xp.degree(),yp.degree(),flush=True)

"""Prepare exact full-input provenance and shape-membership certificates.

Requires the regenerated all400 primitive positive syzygies and the output
of level25_plus_poles_even_prepare.py 1. Does not start a subprocess.
"""
from pathlib import Path
import json

base = Path(__file__).parent
rows = json.loads((base / 'level25_plus_poles_chart1_rows.json').read_text())
shape = json.loads((base / 'level25_plus_poles_chart1_shape.json').read_text())
assert len(rows) == 15 and len(shape['P']) == 68 and len(shape['H']) == 67
source = Path('/tmp/level25_plus_poles_even_chart1_rational.m').read_text()
source = source.split('I:=ideal<R|Q>;')[0]
source += 'I:=ideal<R|Q>; G:=GroebnerBasis(I:GlobalModular:=false);\n'
source += 'assert #G eq 79; Selected:=[R|' + ','.join(rows) + '];\n'
source += 'assert &and[f in I:f in Selected]; print "PASS_FULL_INPUT_PROVENANCE";\n'
source += 'S<t,u,B,A,Y,X>:=PolynomialRing(Rationals(),6,"grevlex");\n'
source += 'P:=[S|' + ','.join(rows) + ',t*A*X*Y-1];\n'
source += 'I:=ideal<S|P>;G:=GroebnerBasis(I:GlobalModular:=false);\n'
source += 'assert Dimension(I) eq 0; assert QuotientDimension(I) eq 70;\n'
for name in ('P', 'H'):
    polynomial = '+'.join(f'({c})*X^{j}' for j,c in enumerate(shape[name]))
    source += f'{name}shape:={polynomial};\n'
source += '''
assert (X-4)*Pshape in I;
J:=I+ideal<S|X-4>;G:=GroebnerBasis(J:GlobalModular:=false);
assert A+2 in J;
assert 213*Y^3+4585*Y^2+500*Y+12096 in J;
assert 4585*9^2 gt 213*9^3+500*9+12096;
J:=I+ideal<S|Pshape>;G:=GroebnerBasis(J:GlobalModular:=false);
assert Y-Hshape in J;
print "PASS_POSITIVE_CHART1_ALGEBRA_AND_X4_EXCLUSION";
quit;
'''
out = Path('/tmp/level25_plus_poles_chart1_certificate.m')
out.write_text(source)
print(out)

"""Evaluate saved numerators as polynomials before fraction-field coercion.

This preserves the literal coefficients, but avoids rational-function gcd work
after every monomial addition. It only writes a bounded native Magma input.
"""
from pathlib import Path
import re

raw = Path('/tmp/level25_cusp_aux_minus_reduced_stream.m').read_text().replace('\\','').split(';')
out = raw[0] + ';\nR:=Parent(Numerator(K.1));\n'
names = ['x','y','z','w','a','b','c']
out += ''.join(f'{n}:=R.{i};' for i,n in enumerate(names,1)) + '\n'
for st in raw[1:]:
    if not st.strip():
        continue
    if ':=K!(' not in st:
        out += st + ';\n'
        continue
    lhs,expr = st.split(':=K!(',1)
    expr = expr.strip()[:-1].strip()
    if expr.startswith('('):
        match = re.fullmatch(r'\((.*)\)/\(([^()]*)\)',expr,re.S)
        assert match, expr[-100:]
        out += lhs+':=(K!('+match[1]+'))/(K!('+match[2]+'));\n'
    else:
        out += lhs+':=K!('+expr+');\n'
out += ''.join(f'{n}:=K.{i};' for i,n in enumerate(names,1)) + '\n'
out += 'print "POLY_TABLES_LOADED";\n'
Path('/tmp/level25_cusp_aux_minus_reduced_poly.m').write_text(out)
text = Path('/tmp/level25_cusp_aux_minus_primitive.m').read_text()
text = text.replace('level25_cusp_aux_minus_reduced_stream.m','level25_cusp_aux_minus_reduced_poly.m')
target = Path('/tmp/level25_cusp_aux_minus_primitive_poly.m')
target.write_text(text)
print(target)

"""Compose a bounded primitive-syzygy batch from saved exact reduced tables."""
from pathlib import Path
import sys
import re

base = Path(__file__).parent
limit = int(sys.argv[1]) if len(sys.argv) > 1 else 96
offset = int(sys.argv[2]) if len(sys.argv) > 2 else 0
export_only = 'export' in sys.argv
assert 1 <= limit <= 400
assert 0 <= offset < 400
raw = Path('/tmp/level25_plus_poles_reduced.m').read_text()
stream = 'K<x,y,z,w,a,b,c>:=RationalFunctionField(Rationals(),7);\n'
tables = list(re.finditer(r'(Lres|Jres|Craw):=Matrix\(K,(\d+),(\d+),\[(.*?)\]\);', raw, re.S))
assert len(tables) == 3
for match in tables:
    name, nr, nc, values = match.groups()
    nr, nc = int(nr), int(nc)
    values = values.split(',')
    assert len(values) == nr * nc
    stream += f'{name}:=ZeroMatrix(K,{nr},{nc});\n'
    for index, value in enumerate(values):
        if value.strip() != '0':
            stream += f'{name}[{index // nc + 1},{index % nc + 1}]:=K!({value});\n'
Path('/tmp/level25_plus_poles_reduced_stream.m').write_text(stream)
backend = (base / 'level25_cusp_aux_magma_firstjet_backend.m').read_text()
functions = backend[:backend.index('active:=[i:i in [1..#A]')]
tail = backend[backend.index('active:=[1..#C];cpiv:=[];cops:=[];czero:=[];'):]
tail = tail.replace('eq:=S!0;', 'equation:=S!0;').replace('eq+:=', 'equation+:=')
tail = tail.replace('if eq ne 0 then Append(~P,eq);',
                    'if equation ne 0 then Append(~P,equation);')
tail = tail.replace(' sat:=S.1*S.2*S.3*S.4*(nonzero2 select S.5 else S!1);', '''
 normalized:={@ S| @};
 for f in P do
  es:=[Exponents(m):m in Monomials(f)];
  unit:=&*[S.i^Min([e[i]:e in es]):i in [1..5]];
  q:=f div unit;q/:=LeadingCoefficient(q);Include(~normalized,q);
 end for;
 P:=Setseq(normalized);
 sat:=S.1*S.2*S.3*S.4*S.5;''')
tail = tail.replace(' print "IDEAL_BEGIN",chart,#P;',
    f' Write("/tmp/level25_plus_poles_seed{offset}_chart" cat IntegerToString(chart) '
    'cat ".txt",P : Overwrite:=true);\n print "IDEAL_BEGIN",chart,#P;')
if export_only:
    tail = tail.replace('time G:=GroebnerBasis(ideal<S|P>);', '/* exported for a separate bounded ideal check */')
    tail = tail.replace(' print "IDEAL_RESULT",chart,#G;', '')
    tail = tail.replace(' if #G lt 8 then G;end if;', '')
text = ('Alarm(45); SetMemoryLimit(500000000); SetNthreads(1); SetSeed(1);\n'
        'SetQuitOnError(true);\nload "/tmp/level25_plus_poles_reduced_stream.m";\n'
        f'nonzero2:=true;limit:={limit};seedoffset:={offset};\n' + functions
        + (base / 'level25_plus_poles_residual_syzygies.m').read_text() + '\n' + tail)
out = Path('/tmp/level25_plus_poles_primitive.m')
out.write_text(text)
print(out, 'limit', limit)

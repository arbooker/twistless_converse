"""Reuse the shared exact Q1050 export for the negative/nonzero-lambda2 sector.

Run the shared exporter first with arguments ``-1 nonzero2``.  This adapter
does not alter its mathematical rows; it uses the current shared backend
and sets conservative resource limits in an independently named batch.
"""
from pathlib import Path
import hashlib
import re
import sys

base = Path(__file__).parent
source = Path('/tmp/level25_cusp_aux_magma_firstjet_-1_nonzero2.m')
raw = source.read_text()
marker = '// A,J are exact sparse leading/source matrices'
assert raw.count(marker) == 1
rows = raw.split(marker)[0]
assert rows.startswith('Alarm(150); SetSeed(1);')
rows = rows.replace('Alarm(150); SetSeed(1);',
                    'Alarm(45); SetMemoryLimit(500000000); SetNthreads(1); SetSeed(1);', 1)
# Preserve every coefficient expression exactly, but avoid tens of thousands
# of interpreted sparse-map mutation statements during input construction.
header, body = rows.split('A:=[* *];J:=[* *];\n', 1)
matrices = {'A': [], 'J': []}
entry = re.compile(r'rr\[(\d+)\]:=(.*);')
pending = None
for line in body.splitlines():
    if line == 'rr:=AssociativeArray(Integers());':
        assert pending is None
        pending = []
    elif entry.fullmatch(line):
        col, coefficient = entry.fullmatch(line).groups()
        pending.append(f'<{col},K!({coefficient})>')
    elif line in ('Append(~A,rr);', 'Append(~J,rr);'):
        matrices[line[8]].append(pending)
        pending = None
    else:
        raise AssertionError(line)
assert pending is None and len(matrices['A']) == len(matrices['J'])
rows = header + '''function SparseRow(entries)
 rr:=AssociativeArray(Integers());
 for item in entries do rr[item[1]]:=item[2]; end for;
 return rr;
end function;
'''
for name, matrix in matrices.items():
    rows += name + ':=[*\n' + ',\n'.join(
        'SparseRow([*' + ','.join(row) + '*])' for row in matrix) + '\n*];\n'
rows += 'print "INPUT_READY",#A;\n'
backend = base / 'level25_cusp_aux_magma_firstjet_backend.m'
backend_text = backend.read_text()
# ``eq`` is a Magma comparison token, so use an ordinary variable name.
backend_text = backend_text.replace('eq:=S!0;', 'equation:=S!0;')
backend_text = backend_text.replace('eq+:=', 'equation+:=')
backend_text = backend_text.replace('if eq ne 0 then Append(~P,eq);',
                                    'if equation ne 0 then Append(~P,equation);')
germ = 'germ' in sys.argv
checkpoint = 'checkpoint' in sys.argv
assert not (germ and checkpoint)
if checkpoint:
    needle = 'active:=[1..#C];cpiv:=[];cops:=[];czero:=[];'
    assert backend_text.count(needle) == 1
    backend_text = backend_text.replace(needle,
        (base / 'level25_plus_poles_checkpoint.m').read_text() + '\n' + needle)
if germ:
    needle = 'for i in zeros do\n'
    assert backend_text.count(needle) == 1
    backend_text = backend_text.replace(needle,
        (base / 'level25_plus_poles_germ_backend.m').read_text() + '\n' + needle)
needle = ' print "IDEAL_BEGIN",chart,#P;'
assert backend_text.count(needle) == 1
backend_text = backend_text.replace(needle,
    ' Write("/tmp/level25_cusp_aux_minus_chart" cat IntegerToString(chart) '
    'cat ".txt",P : Overwrite:=true);\n' + needle)
if germ:
    backend_text = backend_text.replace('/tmp/level25_cusp_aux_minus_chart',
                                         '/tmp/level25_cusp_aux_minus_germ_chart')
coerce = '''// The sparse exporter permits literal integer/rational constants.
// Give every entry the common rational-function-field type before reduction.
for i in [1..#A] do
 for j in Keys(A[i]) do A[i][j]:=K!A[i][j]; end for;
 for j in Keys(J[i]) do J[i][j]:=K!J[i][j]; end for;
end for;
'''
batch = (rows + coerce + backend_text).replace('/tmp/level25_plus_poles', '/tmp/level25_cusp_aux_minus')
out = Path('/tmp/level25_cusp_aux_minus_nonzero2' + ('_germ' if germ else '')
           + ('_checkpoint' if checkpoint else '') + '.m')
out.write_text(batch)
print('BACKEND_SHA256', hashlib.sha256(backend.read_bytes()).hexdigest())
print('BATCH_SHA256', hashlib.sha256(out.read_bytes()).hexdigest())
print('BATCH', out)

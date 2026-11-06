"""Independently regenerate N19 firstjet source and audit sparse row54.

No Groebner computation. Native Magma batch is prepared, never launched.
"""
from pathlib import Path
import contextlib, hashlib, json, signal, time

HERE = Path(__file__).resolve().parent
OUT = Path('/tmp/level19_rootind_sparse')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
started = time.time()
signal.alarm(180)
meta = {'status': 'RUNNING', 'sources': {}}
try:
    for name in ['level19_firstjet_certificate.py', 'level19_pole_probe.py',
                 'level19_exact_membership_sparse_prepare.py']:
        meta['sources'][name] = sha(HERE / name)
    src = (HERE / 'level19_firstjet_certificate.py').read_text()
    # Run original rational source construction, not its algebra backend or write.
    src = src[:src.index("Path('/tmp/level19_firstjet_certificate.m').write_text")]
    src = src.replace('# Regenerate the independent proportional-row constraints.',
        'audit_left=[(dict(r),l) for r,l in left]\n# Regenerate the independent proportional-row constraints.')
    ns = {'__file__': str(HERE / 'level19_firstjet_certificate.py')}
    with open(str(OUT) + '_source.log', 'w') as log, contextlib.redirect_stdout(log):
        exec(compile(src, str(HERE / 'level19_firstjet_certificate.py'), 'exec'), ns)
    head = ns['head']
    Path(str(OUT) + '_header.m').write_text(head)
    expected_head = Path('/tmp/level19_firstjet_certificate.m').read_text().split('Al:=')[0]
    assert head.strip() == expected_head.strip(), 'regenerated header differs'
    # The exporter selects six columns: prove no unrecorded coordinate was dropped.
    assert len(ns['audit_left']) == 60 and len(ns['orows']) == 27, 'matrix row count'
    assert all(set(r) <= set(ns['cols']) for r,l in ns['audit_left']), 'firstjet dropped coordinate'
    assert all(set(r) <= {18,42,72} for r,l in ns['orows'])
    assert len(ns['safe']) == 15
    meta['header_sha256'] = hashlib.sha256(head.encode()).hexdigest()
    meta['matrix_support'] = {'firstjet_rows':60,'firstjet_columns':ns['cols'],
                             'leading_rows':27,'leading_columns':[18,42,72],
                             'safe_polynomials':15}
    # Retain an independent copy of the regenerated exact header.
    Path(str(OUT) + '_header.m').write_text(head)
    fast = Path('/tmp/level19_exact_membership_sparse_fast.m')
    meta['comparison_sparse_export_sha256'] = sha(fast)
    body = r'''
assert Nrows(A) eq 60 and Ncols(A) eq 6;
Ap:=ZeroMatrix(R,60,6);
for i in [1..60] do
 d:=LCM([Denominator(A[i,j]):j in [1..6]]);
 assert IsDivisibleBy(x^7*y^4*a,d);
 for j in [1..6] do Ap[i,j]:=R!(d*A[i,j]);end for;
end for;
Al:=Submatrix(Ap,1,1,60,3); Ar:=Submatrix(Ap,1,4,60,3);
rows:=[1,37,43,54];
weights:=[(-1)^j*Determinant(Matrix(R,[Eltseq(Al[rows[k]]):k in [1..4]|k ne j])):j in [1..4]];
assert &+[weights[j]*Al[rows[j]]:j in [1..4]] eq 0;
divisor:=GCD(weights); assert divisor ne 0;
primitive:=[ExactQuotient(w,divisor):w in weights];
assert &+[primitive[j]*Al[rows[j]]:j in [1..4]] eq 0;
assert GCD(primitive) eq R!1;
v:=Vector(R,[-(x^4+(a^2-2)*x^2+1),x*a*(y^2+1),-x*a*(y^2+1)]);
q:=&+[primitive[j]*(&+[Ar[rows[j],k]*v[k]:k in [1..3]]):j in [1..4]];
assert q ne 0;
safe:=x*y*a*(y^2+1)*(x^4-1)*(x^2-2*x*a+4);
removed:=R!1;
repeat
 g:=GCD(q,safe);
 if TotalDegree(g) eq 0 then break;end if;
 assert IsDivisibleBy(safe,g);
 q:=ExactQuotient(q,g); removed*:=g;
until false;
scale:=LeadingCoefficient(q);q/:=scale;
EE:=[Exponents(m):m in Monomials(q)]; CC:=Coefficients(q);
dx:=Min([e[1]-e[4]:e in EE]);dy:=Min([e[2]-e[5]:e in EE]);da:=Min([e[4]:e in EE]);
FF:=[[e[5],e[4]-da,e[3],(e[2]-e[5]-dy) div 2,(e[1]-e[4]-dx) div 2]:e in EE];
for i in [1..#EE] do
 e:=EE[i];f:=FF[i];
 assert (e[1]-e[4]-dx) mod 2 eq 0 and (e[2]-e[5]-dy) mod 2 eq 0;
 assert Min(f) ge 0;
 assert e eq [2*f[5]+f[2]+dx+da,2*f[4]+f[1]+dy,f[3],f[2]+da,f[1]];
end for;
'''
    # The comparison file creates its ring and list only; no algebra computations.
    body += fast.read_text()
    body += r'''
candidate:=Polynomial(CC,[Monomial(S,e):e in FF]);
assert candidate eq PP[15];
assert #Monomials(candidate) eq 130 and TotalDegree(candidate) eq 9;
assert K!q eq Evaluate(candidate,[K!(b*y),K!(a*x),K!z,K!(y^2),K!(x^2)])*(K!x)^(dx+da)*(K!y)^dy*(K!a)^da;
print "PASS_SOURCE_MATRIX_SUPPORT_AND_ROW54_PRIMITIVE_SYZYGY";
print "REMOVED",Factorization(removed),"SCALE",scale;
print "COMPACT_FACTORS",dx+da,dy,da;
print "PASS_EXACT_COMPACT_INDEX15_130TERMS_DEGREE9";
PrintFile("/tmp/level19_rootind_sparse_native.pass","PASS independent sparse syzygy and compactification":Overwrite:=true);
UnsetOutputFile();quit;
'''
    prefix = 'SetOutputFile("/tmp/level19_rootind_sparse_native.log":Overwrite:=true);SetQuitOnError(true);SetNthreads(1);SetMemoryLimit(500000000);Alarm(60);SetGBGlobalModular(false);\n'
    batch = Path(str(OUT) + '_native.m')
    batch.write_text(prefix + head + body)
    meta.update(status='PASS_SOURCE_REGENERATION_NATIVE_PREPARED',batch_sha256=sha(batch))
except BaseException as exc:
    meta.update(status='FAIL',error=repr(exc))
    raise
finally:
    meta['elapsed_seconds'] = time.time()-started
    Path(str(OUT) + '_source_completion.json').write_text(json.dumps(meta,indent=2)+'\n')
print(meta['status'], meta['elapsed_seconds'])

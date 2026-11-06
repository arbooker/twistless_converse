"""Clean N19 21-input producer. No existing /tmp input and no GB required.

Run this Python file, then run the direct Magma command it prints. Every
run uses a unique scratch directory. All mathematical inputs are regenerated
from the original pole-probe and firstjet exporter source in this directory.
"""
from pathlib import Path
from datetime import datetime,timezone
import contextlib,hashlib,json,signal,time
HERE=Path(__file__).resolve().parent
run=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
out=Path('/tmp')/('level19_rootind_sparse_reproduce_'+run)
out.mkdir()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
meta={'status':'RUNNING','run':str(out)}
signal.alarm(180)
try:
 src=(HERE/'level19_firstjet_certificate.py').read_text()
 src=src[:src.index("body=r'''")]
 src=src.replace('# Regenerate the independent proportional-row constraints.',
  'audit_left=[(dict(r),l) for r,l in left]\n# Regenerate the independent proportional-row constraints.')
 ns={'__file__':str(HERE/'level19_firstjet_certificate.py')}
 with (out/'source.log').open('w') as log,contextlib.redirect_stdout(log):
  exec(compile(src,str(HERE/'level19_firstjet_certificate.py'),'exec'),ns)
 assert len(ns['audit_left'])==60 and len(ns['orows'])==27 and len(ns['safe'])==15
 assert all(set(r)<=set(ns['cols']) for r,l in ns['audit_left'])
 assert all(set(r)<={18,42,72} for r,l in ns['orows'])
 # Independent termwise compactification of freshly generated Safe15.
 compact=[]
 for p in ns['safe']:
  terms=p.terms()
  dx=min(e[0]-e[3] for e,c in terms);dy=min(e[1]-e[4] for e,c in terms);da=min(e[3] for e,c in terms)
  q={}
  for e,c in terms:
   assert (e[0]-e[3]-dx)%2==0 and (e[1]-e[4]-dy)%2==0
   f=(e[4],e[3]-da,e[2],(e[1]-e[4]-dy)//2,(e[0]-e[3]-dx)//2)
   assert min(f)>=0 and f not in q
   assert (2*f[4]+f[1]+dx+da,2*f[3]+f[0]+dy,f[2],f[1]+da,f[0])==e
   q[f]=c
  scale=q[min(q)]
  compact.append({e:c/scale for e,c in q.items()})
 safe='S<Bb,Aa,Zz,Yy,Xx>:=PolynomialRing(Rationals(),5,"grevlex");\nSS:=[S|];\n'
 for q in compact:
  safe+='Append(~SS,Polynomial(['+','.join(str(c) for e,c in sorted(q.items()))+'],[Monomial(S,e):e in ['+','.join(str(list(e)) for e,c in sorted(q.items()))+']]));\n'
 body=r'''
Ap:=ZeroMatrix(R,60,6);
for i in [1..60] do
 d:=LCM([Denominator(A[i,j]):j in [1..6]]);
 assert IsDivisibleBy(x^7*y^4*a,d);
 for j in [1..6] do Ap[i,j]:=R!(d*A[i,j]);end for;
end for;
Al:=Submatrix(Ap,1,1,60,3); Ar:=Submatrix(Ap,1,4,60,3);
ids:=[2,3,4,5,27,28,29,34,38,39,40,42,44,46,54];
NN:=[S|];
for nn in [1..#ids] do
 rows:=[1,37,43,ids[nn]];
 weights:=[(-1)^j*Determinant(Matrix(R,[Eltseq(Al[rows[k]]):k in [1..4]|k ne j])):j in [1..4]];
 divisor:=GCD(weights); assert divisor ne 0;
 weights:=[ExactQuotient(w,divisor):w in weights];
 assert &+[weights[j]*Al[rows[j]]:j in [1..4]] eq 0;
 v:=Vector(R,[-(x^4+(a^2-2)*x^2+1),x*a*(y^2+1),-x*a*(y^2+1)]);
 q:=&+[weights[j]*(&+[Ar[rows[j],k]*v[k]:k in [1..3]]):j in [1..4]];
 assert q ne 0;
 safe:=x*y*a*(y^2+1)*(x^4-1)*(x^2-2*x*a+4);
 repeat
  g:=GCD(q,safe);
  if TotalDegree(g) eq 0 then break;end if;
  assert IsDivisibleBy(safe,g);q:=ExactQuotient(q,g);
 until false;
 q/:=LeadingCoefficient(q);
 EE:=[Exponents(m):m in Monomials(q)]; CC:=Coefficients(q);
 dx:=Min([e[1]-e[4]:e in EE]);dy:=Min([e[2]-e[5]:e in EE]);da:=Min([e[4]:e in EE]);
 FF:=[[e[5],e[4]-da,e[3],(e[2]-e[5]-dy) div 2,(e[1]-e[4]-dx) div 2]:e in EE];
 for i in [1..#EE] do
  e:=EE[i];f:=FF[i];
  assert (e[1]-e[4]-dx) mod 2 eq 0 and (e[2]-e[5]-dy) mod 2 eq 0 and Min(f) ge 0;
  assert e eq [2*f[5]+f[2]+dx+da,2*f[4]+f[1]+dy,f[3],f[2]+da,f[1]];
 end for;
 candidate:=Polynomial(CC,[Monomial(S,e):e in FF]);
 assert K!q eq Evaluate(candidate,[K!(b*y),K!(a*x),K!z,K!(y^2),K!(x^2)])*(K!x)^(dx+da)*(K!y)^dy*(K!a)^da;
 Append(~NN,candidate);
 print "PASS_FRESH_SYZYGY",nn,ids[nn];
end for;
for i in [1..15] do
 ratio:=(K!Safe[i])/Evaluate(SS[i],[K!(b*y),K!(a*x),K!z,K!(y^2),K!(x^2)]);
 assert #Monomials(Numerator(ratio)) eq 1 and #Monomials(Denominator(ratio)) eq 1;
 assert Exponents(Monomials(Numerator(ratio))[1])[5] eq 0 and Exponents(Monomials(Denominator(ratio))[1])[5] eq 0;
end for;
PP:=SS cat [NN[i]:i in [8,11,12,13,14,15]];assert #PP eq 21;
PrintFile(OUTPUT,"S<B,A,Z,Y,X>:=PolynomialRing(Rationals(),5,\"grevlex\");\nPP:=[S|];":Overwrite:=true);
for q in PP do
 PrintFile(OUTPUT,"Append(~PP,Polynomial(" cat Sprint(Coefficients(q)) cat ",[Monomial(S,e):e in " cat Sprint([Exponents(m):m in Monomials(q)]) cat "]));");
end for;
print "PASS_CLEAN_SOURCE_TO_SELFCONTAINED21";
PrintFile(COMPLETION,"{\"completed\":true,\"status\":\"PASS_CLEAN21\"}":Overwrite:=true);
UnsetOutputFile();quit;
'''
 body=body.replace('OUTPUT',json.dumps(str(out/'inputs21.m'))).replace('COMPLETION',json.dumps(str(out/'native.completion.json')))
 prefix='SetOutputFile('+json.dumps(str(out/'native.log'))+':Overwrite:=true);SetQuitOnError(true);SetNthreads(1);SetMemoryLimit(500000000);Alarm(120);SetGBGlobalModular(false);\n'
 batch=out/'produce.m';batch.write_text(prefix+ns['head']+safe+body)
 meta.update(status='PASS_SOURCE_NATIVE_PREPARED',sources={n:sha(HERE/n) for n in ['level19_firstjet_certificate.py','level19_pole_probe.py','level19_rootind_sparse_reproduce.py']},batch_sha256=sha(batch),header_sha256=hashlib.sha256(ns['head'].encode()).hexdigest())
except BaseException as e:
 meta.update(status='FAIL',error=repr(e));raise
finally:
 (out/'source.completion.json').write_text(json.dumps(meta,indent=2)+'\n')
print('magma -b -l500000000 -t1 '+str(batch))
print('OUTPUT '+str(out/'inputs21.m'))
print('SOURCE_RECORD '+str(out/'source.completion.json'))

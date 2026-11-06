"""Audit all fifteen sparse syzygies against independently rebuilt source."""
from pathlib import Path
import hashlib,json
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
head=Path('/tmp/level19_rootind_sparse_header.m')
rec=json.loads(Path('/tmp/level19_rootind_sparse_source_completion.json').read_text())
assert rec['status']=='PASS_SOURCE_REGENERATION_NATIVE_PREPARED'
assert sha(head)==rec['header_sha256']
fast=Path('/tmp/level19_exact_membership_sparse_fast.m')
oldfast=Path('/tmp/level19_sparse_poles_compactall_fast.m')
assert sha(fast)==rec['comparison_sparse_export_sha256']
body=r'''
Ap:=ZeroMatrix(R,60,6);
for i in [1..60] do
 d:=LCM([Denominator(SourceMatrix[i,j]):j in [1..6]]);
 assert IsDivisibleBy(x^7*y^4*a,d);
 for j in [1..6] do Ap[i,j]:=R!(d*SourceMatrix[i,j]);end for;
end for;
Al:=Submatrix(Ap,1,1,60,3); Ar:=Submatrix(Ap,1,4,60,3);
ids:=[2,3,4,5,27,28,29,34,38,39,40,42,44,46,54];
assert #PP eq #ids;
for nn in [1..#ids] do
 rows:=[1,37,43,ids[nn]];
 weights:=[(-1)^j*Determinant(Matrix(R,[Eltseq(Al[rows[k]]):k in [1..4]|k ne j])):j in [1..4]];
 assert &+[weights[j]*Al[rows[j]]:j in [1..4]] eq 0;
 divisor:=GCD(weights); assert divisor ne 0;
 primitive:=[ExactQuotient(w,divisor):w in weights];
 assert &+[primitive[j]*Al[rows[j]]:j in [1..4]] eq 0;
 assert GCD(primitive) eq R!1;
 v:=Vector(R,[-(x^4+(a^2-2)*x^2+1),x*a*(y^2+1),-x*a*(y^2+1)]);
 q:=&+[primitive[j]*(&+[Ar[rows[j],k]*v[k]:k in [1..3]]):j in [1..4]];
 assert q ne 0;
 safe:=x*y*a*(y^2+1)*(x^4-1)*(x^2-2*x*a+4);removed:=R!1;
 repeat
  g:=GCD(q,safe);
  if TotalDegree(g) eq 0 then break;end if;
  assert IsDivisibleBy(safe,g);
  q:=ExactQuotient(q,g);removed*:=g;
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
 candidate:=Polynomial(CC,[Monomial(S,e):e in FF]);
 assert candidate eq PP[nn];
 assert K!q eq Evaluate(candidate,[K!(b*y),K!(a*x),K!z,K!(y^2),K!(x^2)])*(K!x)^(dx+da)*(K!y)^dy*(K!a)^da;
 print "PASS_SPARSE_SOURCE_ROW",nn,ids[nn],#Monomials(candidate),TotalDegree(candidate);
 print "COMPACT_FACTORS",dx+da,dy,da;
end for;
print "PASS_ALL15_PRIMITIVE_SYZYGIES_AND_EXACT_INVERSE_COMPACTIFICATION";
'''
tail=r'''
assert #Safe eq 15;
for i in [1..15] do
 compact:=Evaluate(PP[i],[K!(b*y),K!(a*x),K!z,K!(y^2),K!(x^2)]);
 assert compact ne 0;
 ratio:=(K!Safe[i])/compact;
 assert #Monomials(Numerator(ratio)) eq 1 and #Monomials(Denominator(ratio)) eq 1;
 assert Exponents(Monomials(Numerator(ratio))[1])[5] eq 0;
 assert Exponents(Monomials(Denominator(ratio))[1])[5] eq 0;
 print "PASS_SAFE15_ORIGINAL_TO_COMPACT",i,ratio;
end for;
print "PASS_SAFE15_AND_SIX_SPARSE_FINAL_INPUT_PROVENANCE";
PrintFile("/tmp/level19_rootind_sparse_all_native.pass","PASS all15 sparse syzygies and originalSafe15 compactification":Overwrite:=true);
UnsetOutputFile();quit;
'''
prefix='SetOutputFile("/tmp/level19_rootind_sparse_all_native.log":Overwrite:=true);SetQuitOnError(true);SetNthreads(1);SetMemoryLimit(500000000);Alarm(120);SetGBGlobalModular(false);\n'
batch=Path('/tmp/level19_rootind_sparse_all_native.m')
batch.write_text(prefix+head.read_text()+'SourceMatrix:=A;\n'+fast.read_text()+body+oldfast.read_text()+tail)
rec['all15_batch_sha256']=sha(batch)
rec['all15_prepare_sha256']=sha(__file__)
rec['compact_old_input_sha256']=sha(oldfast)
Path('/tmp/level19_rootind_sparse_all_prepared.json').write_text(json.dumps(rec,indent=2)+'\n')
print('PREPARED',sha(batch))

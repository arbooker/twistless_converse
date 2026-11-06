"""Prepare exact sparse syzygies; does not launch an algebra process."""
from pathlib import Path
import hashlib, json
original = Path('/tmp/level19_firstjet_certificate.m')
header = original.read_text().split('Al:=')[0]
body = r'''
Ap:=ZeroMatrix(R,60,6);
assert forall{c:c in Eltseq(A)|IsDivisibleBy(x^7*y^4*a,Denominator(c))};
for i in [1..60] do
 den:=LCM([Denominator(A[i,j]):j in [1..6]]);
 for j in [1..6] do Ap[i,j]:=R!(den*A[i,j]);end for;
end for;
Al:=Submatrix(Ap,1,1,60,3);Ar:=Submatrix(Ap,1,4,60,3);
base:=[];
for i in [1,37,42,10,6,43,46,47] cat [1..60] do
 if Rank(Matrix(K,[Eltseq(Al[j]):j in base cat [i]])) gt #base then Append(~base,i);end if;
 if #base eq 3 then break;end if;
end for;
print "BASE",base;
v:=Vector(R,[-(x^4+(a^2-2)*x^2+1),x*a*(y^2+1),-x*a*(y^2+1)]);
polys:=[];ids:=[];
for i in [1..60] do
 if i in base then continue;end if;
 rows:=base cat [i];
 weights:=[(-1)^j*Determinant(Matrix(R,[Eltseq(Al[rows[k]]):k in [1..4]|k ne j])):j in [1..4]];
 g:=GCD(weights);assert g ne 0;
 weights:=[ExactQuotient(w,g):w in weights];
 assert &+[weights[j]*Al[rows[j]]:j in [1..4]] eq 0;
 q:=&+[weights[j]*(&+[Ar[rows[j],k]*v[k]:k in [1..3]]):j in [1..4]];
 if q eq 0 then continue;end if;
 safe:=x*y*a*(y^2+1)*(x^4-1)*(x^2-2*x*a+4);
 repeat
   g:=GCD(q,safe);
   if TotalDegree(g) eq 0 then break;end if;
   q:=ExactQuotient(q,g);
 until false;
 q:=q/LeadingCoefficient(q);
 if q notin polys then Append(~polys,q);Append(~ids,i);end if;
end for;
S<Bb,Aa,Zz,Yy,Xx>:=PolynomialRing(Rationals(),5,"grevlex");
PP:=[];
for p in polys do
 EE:=[Exponents(m):m in Monomials(p)];CC:=Coefficients(p);
 dx:=Min([e[1]-e[4]:e in EE]);dy:=Min([e[2]-e[5]:e in EE]);da:=Min([e[4]:e in EE]);
 assert forall{e:e in EE|(e[1]-e[4]-dx) mod 2 eq 0 and (e[2]-e[5]-dy) mod 2 eq 0};
 q:=Polynomial(CC,[Monomial(S,[e[5],e[4]-da,e[3],(e[2]-e[5]-dy) div 2,(e[1]-e[4]-dx) div 2]):e in EE]);
 assert K!p eq Evaluate(q,[K!(b*y),K!(a*x),K!z,K!(y^2),K!(x^2)])*(K!x)^(dx+da)*(K!y)^dy*(K!a)^da;
 Append(~PP,q);
end for;
out:="/tmp/level19_exact_membership_sparse_fast.m";
PrintFile(out,"S<B,A,Z,Y,X>:=PolynomialRing(Rationals(),5,\"grevlex\");\nPP:=[];":Overwrite:=true);
for i in [1..#PP] do
 q:=PP[i];print i,ids[i],#Monomials(q),TotalDegree(q);
 PrintFile(out,"Append(~PP,Polynomial(" cat Sprint(Coefficients(q)) cat ",[Monomial(S,e):e in " cat Sprint([Exponents(m):m in Monomials(q)]) cat "]));");
end for;
PrintFile("/tmp/level19_exact_membership_sparse.pass","PASS exact sparse syzygies":Overwrite:=true);
UnsetOutputFile();quit;
'''
prefix='SetOutputFile("/tmp/level19_exact_membership_sparse.log":Overwrite:=true);SetQuitOnError(true);SetNthreads(1);SetMemoryLimit(500000000);Alarm(45);\n'
Path('/tmp/level19_exact_membership_sparse.m').write_text(prefix+header+body)
sources=[Path(__file__),Path(__file__).with_name('level19_firstjet_certificate.py'),Path(__file__).with_name('level19_pole_probe.py')]
manifest={'original_export_sha256':hashlib.sha256(original.read_bytes()).hexdigest(),
 'original_header_sha256':hashlib.sha256(header.encode()).hexdigest(),
 'sources':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
 'batch_sha256':hashlib.sha256((prefix+header+body).encode()).hexdigest(),
 'base_rows':[1,37,43], 'decisive_original_row':54,'decisive_export_index':15,
 'status':'prepared; successful run requires external exact PASS marker'}
Path('/tmp/level19_exact_membership_sparse_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')

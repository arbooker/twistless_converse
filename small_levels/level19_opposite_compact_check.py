"""Export the complete, exact opposite-sign generic pole certificate.

Run level19_opposite_firstjet_export.py first, then this script, then
magma -b -l 500000000 /tmp/level19_opposite_compact_verified.m
The Magma assertions check polynomial row syzygies against the regenerated
56-by-6 matrix and the exact rational Groebner basis, without numerical
specialization. G=0 is handled by level19_opposite_gzero_check.py.
"""
from pathlib import Path
import hashlib
import json
source = Path("/tmp/level19_opposite_firstjet_certificate.m").read_text()
header = source.split("Al:=")[0]
weights = json.loads(Path(__file__).with_name("level19_opposite_syzygies.json").read_text())
for i, row in enumerate(weights):
    header += "L" + str(i) + ":=Vector(K,[" + ",".join(
        row.get(str(j), "0").replace("**", "^") for j in range(56)) + "]);\n"
body = r'''Al:=Submatrix(A,1,1,56,3); Ar:=Submatrix(A,1,4,56,3);
v:=Transpose(Matrix(Vector(K,[-(x^4+(a^2-2)*x^2+1),x*a*(y^2+1),-x*a*(y^2+1)])));
P:=[Numerator(c):c in Eltseq(B*v)|c ne 0];
for L in [L0,L1,L2] do
 assert forall{c:c in Eltseq(L)|Denominator(c) eq 1};
 assert L*Al eq 0;
 c:=Eltseq(Matrix(L)*Ar*v)[1];assert c ne 0;
 Append(~P,Numerator(c));
end for;
S<Bb,Aa,T,Y,X>:=PolynomialRing(Rationals(),5,"grevlex");
PP:=[];
for p in P do
 if Degree(p,z) ne 0 then continue;end if;
 EE:=[Exponents(m):m in Monomials(p)];
 dx:=Min([e[1]-e[4]:e in EE]);dy:=Min([e[2]-e[5]:e in EE]);da:=Min([e[4]:e in EE]);
 assert forall{e:e in EE|(e[1]-e[4]-dx) mod 2 eq 0 and (e[2]-e[5]-dy) mod 2 eq 0};
 q:=&+[S!Coefficients(p)[j]*Bb^EE[j][5]*Aa^(EE[j][4]-da)*Y^((EE[j][2]-EE[j][5]-dy) div 2)*X^((EE[j][1]-EE[j][4]-dx) div 2):j in [1..#EE]];
 q:=q/LeadingCoefficient(q);
 if q notin PP then Append(~PP,q);end if;
end for;
print "compact constraints",[#Monomials(q):q in PP];
Append(~PP,T*X*Y*Aa*(Y+1)*(X^2-1)*(X-2*Aa+4)-1);
time GB:=GroebnerBasis(ideal<S|PP>);
expected:=[Bb+5,Aa+3,T+1/226800,Y-9,X-4];
assert GB eq expected;
print "PASS: opposite-sign generic pole constraints",GB;
quit;
'''
out = Path("/tmp/level19_opposite_compact_verified.m")
out.write_text("SetNthreads(1);\n" + header + body)
print(out)
print("SHA256", hashlib.sha256(out.read_bytes()).hexdigest())

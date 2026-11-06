"""Export and audit the opposite-sign G=0 certificate over Q.

First run level19_opposite_firstjet_export.py. This script derives a
small Magma input from its complete regenerated matrices; execute the
printed file with Magma. No Magma process is launched automatically.
"""
from pathlib import Path
import hashlib
source = Path("/tmp/level19_opposite_firstjet_certificate.m").read_text()
header = source.split("Al:=")[0]
body = r'''v:=Transpose(Matrix(Vector(K,[-(x^4+(a^2-2)*x^2+1),x*a*(y^2+1),-x*a*(y^2+1)])));
P:=Safe cat [Numerator(c):c in Eltseq(B*v)|c ne 0];
S<X,Y,Z,AA,BB,TT>:=PolynomialRing(Rationals(),6,"grevlex");
P:=[Evaluate(p,[X,Y,Z,AA,BB]):p in P];
P cat:= [X^2+2,AA*X-1,TT*X*Y*Z*AA*(Y^2+1)*(X^4-1)-1];
GB:=GroebnerBasis(ideal<S|P>);
assert GB eq [S!1];
print "PASS: opposite-sign G=0 pole branch has rational basis [1]";
quit;
'''
out = Path("/tmp/level19_opposite_gzero_verified.m")
out.write_text("SetNthreads(1);\n" + header + body)
print(out)
print("SHA256", hashlib.sha256(out.read_bytes()).hexdigest())

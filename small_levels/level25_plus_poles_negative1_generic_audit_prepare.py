"""Independent exact input/Cramer/substitution audit for generic negative chart1.

Consumes the independently regenerated and normalized chart1, matches all100
chosen raw rational rows literally, and checks every denominator removed.
The finite-named source is only a rational expression list; its coefficients
are checked against the independent characteristic-zero source before use.
"""
from pathlib import Path
from fractions import Fraction
import re

fresh = Path('/tmp/level25_root_negative_first_even1_rational_pure.m').read_text()
original = Path('/tmp/level25_cusp_aux_minus_even1_finite_pure.m').read_text()
freshrows = re.findall(r'Append\(~P,(.*?)\);', fresh, re.S)
chosen = re.findall(r'Append\(~P,(.*?)\);', original, re.S)[:-1][:100]
assert len(freshrows) == 203 and len(chosen) == 100
assert all(p in freshrows for p in chosen)
names = ['u','B','A','Y','X','t']
source = '''Alarm(45);SetMemoryLimit(500000000);SetNthreads(1);
SetQuitOnError(true);SetGBGlobalModular(false);
R<u,B,A,Y,X,t>:=PolynomialRing(Rationals(),6,"grevlex");
P:=[R|];
'''
for row in chosen:
    coeffs, exps = [], []
    for sign, term in re.findall(r'([+-]?)([^+-]+)', re.sub(r'\s+','',row)):
        coefficient = Fraction(-1 if sign == '-' else 1)
        exponents = [0]*6
        for factor in term.split('*'):
            match = re.fullmatch(r'(u|B|A|Y|X|t)(?:\^(\d+))?', factor)
            if match:
                exponents[names.index(match[1])] += int(match[2] or 1)
            else:
                coefficient *= Fraction(factor)
        coeffs.append(str(coefficient))
        exps.append(str(exponents))
    source += 'Append(~P,Polynomial(['+','.join(coeffs)+'],[Monomial(R,e):e in ['+','.join(exps)+']]));\n'
source += '''
f:=P[1];g:=P[3]; assert IsDivisibleBy(f,A+1);f:=f div (A+1);
f0:=Evaluate(f,[R!0,R!0,A,Y,X,t]);g0:=Evaluate(g,[R!0,R!0,A,Y,X,t]);
fu:=Evaluate(f,[R!1,R!0,A,Y,X,t])-f0;
fb:=Evaluate(f,[R!0,R!1,A,Y,X,t])-f0;
gu:=Evaluate(g,[R!1,R!0,A,Y,X,t])-g0;
gb:=Evaluate(g,[R!0,R!1,A,Y,X,t])-g0;
assert f eq fb*B+fu*u+f0;assert g eq gb*B+gu*u+g0;
D0:=A*(X-Y)+X^3-X^2-X;U:=A*X*(X-1)+X*Y+X-Y;
V:=A^3*X*Y-A^3*X+A^2*X*Y+2*A^2*X-A^2*Y+A*X^3*Y-A*X^3-2*A*X^2*Y+3*A*X^2-2*A*X+A*Y-2*X^2*Y-2*X^2-X*Y^2+2*X*Y+X+Y^2-Y;
assert fb*gu-gb*fu eq -A*X^2*Y*D0;
assert -f0*gu+g0*fu eq -A*X*Y*V;
assert -fb*g0+gb*f0 eq -A*X^2*Y*U;
print "PASS_INDEPENDENT_INPUT_AND_CRAMER";
K<a0,y0,x0>:=RationalFunctionField(Rationals(),3);
d0:=a0*(x0-y0)+x0^3-x0^2-x0;
u0:=Evaluate(U,[K!0,K!0,a0,y0,x0,K!0])/d0;
b0:=Evaluate(V,[K!0,K!0,a0,y0,x0,K!0])/(x0*d0);
S:=Parent(Numerator(a0));AssignNames(~S,["A","Y","X"]);
D:=S.1*(S.3-S.2)+S.3^3-S.3^2-S.3;
units:=[S.1,S.2,S.3,S.1+1,S.1+2,D];
Q:={@ S| @};
for p in P do
 value:=Evaluate(p,[u0,b0,a0,y0,x0,K!1]);
 if value eq 0 then continue;end if;
 den:=Denominator(value);
 for unit in units do
  while IsDivisibleBy(den,unit) do den:=den div unit;end while;
 end for;
 assert TotalDegree(den) eq 0;
 num:=Numerator(value);
 for unit in units do
  while IsDivisibleBy(num,unit) do num:=num div unit;end while;
 end for;
 num/:=LeadingCoefficient(num);Include(~Q,num);
end for;
assert #Q eq 14;
Write("/tmp/level25_plus_poles_negative1_generic_audit_relations.txt",Setseq(Q):Overwrite:=true);
print "PASS_INDEPENDENT_GENERIC_RELATIONS",#Q;
quit;
'''
out = Path('/tmp/level25_plus_poles_negative1_generic_audit_export.m')
out.write_text(source)
print(out)

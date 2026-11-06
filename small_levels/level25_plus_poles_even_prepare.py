"""Exact unit-monomial normalization under A=a*x, B=b*y, C=c*w.

The exponent parity is checked term by term, so no parameter locus is lost.
The finite option is diagnostic only. Rational checks disable GlobalModular.
"""
from pathlib import Path
import sys

chart = int(sys.argv[1])
assert chart in (1, 2)
finite = 'finite' in sys.argv
export = 'export' in sys.argv
field = 'GF(32003)' if finite else 'Rationals()'
variant = 'finite' if finite else 'rational'
source = Path(f'/tmp/level25_plus_poles_seed0_chart{chart}.txt').read_text().strip()
assert source[0] == '[' and source[-1] == ']'
text = f'''Alarm(45); SetMemoryLimit(500000000); SetNthreads(1);
SetQuitOnError(true);SetGBGlobalModular(false);
S<x,y,z,w,a,b,c,v1,t>:=PolynomialRing({field},9,"grevlex");
P:=[S|];
'''
text += ''.join('Append(~P,S!(' + p + '));\n' for p in source[1:-1].split(','))
text += f'''
R<u,C,B,A,Z,W,Y,X,t>:=PolynomialRing({field},9,"grevlex");
normalized:={{@ R| @}};
for f in P do
 if Degree(f,9) gt 0 then continue;end if;
 mons:=Monomials(f);cs:=Coefficients(f);
 es:=[Exponents(m):m in mons];
 shifted:=[[e[1]-e[5],e[2]-e[6],e[3],e[4]-e[7]]:e in es];
 mins:=[Min([e[j]:e in shifted]):j in [1..4]];
 assert &and[IsEven(e[j]-mins[j]):e in shifted,j in [1..4]];
 q:=R!0;
 for i in [1..#es] do
  e:=es[i];d:=[(shifted[i][j]-mins[j]) div 2:j in [1..4]];
  exponents:=[e[8],e[7],e[6],e[5],d[3],d[4],d[2],d[1],0];
  q+:=cs[i]*&*[R.j^exponents[j]:j in [1..9]];
 end for;
 q/:=LeadingCoefficient(q);Include(~normalized,q);
end for;
print "Z_DEPENDENT_ROWS",#[q:q in normalized|Degree(q,5) gt 0];
Q:=Setseq(normalized);
Append(~Q,t*X*Y*Z*W*A-1);
print "EXACT_EVEN_NORMALIZATION",#Q;
Write("/tmp/level25_plus_poles_even_chart{chart}_{variant}.txt",Q : Overwrite:=true);
'''
if not export:
    text += '''I:=ideal<R|Q>;time G:=GroebnerBasis(I:GlobalModular:=false);
print "GB",#G,"DIMENSION",Dimension(I);
for g in G do if #Monomials(g) le 12 then print g;end if;end for;
'''
    text += f'Write("/tmp/level25_plus_poles_even_gb_chart{chart}_{variant}.txt",G : Overwrite:=true);\n'
text += 'quit;\n'
out = Path(f'/tmp/level25_plus_poles_even_chart{chart}_{variant}.m')
out.write_text(text)
print(out)

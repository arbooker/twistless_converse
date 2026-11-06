"""Prepare exact characteristic-zero ideal-membership checks for chart two.

First regenerate the full positive/nonzero2 primitive-syzygy tables and run
level25_plus_poles_even_prepare.py 2. No input or coefficient is specialized.
"""
from pathlib import Path

source = Path('/tmp/level25_plus_poles_even_chart2_rational.m').read_text()
assert source.count('I:=ideal<R|Q>;') == 1
source = source.split('I:=ideal<R|Q>;')[0]
source += '''
I:=ideal<R|Q>;
G:=GroebnerBasis(I:GlobalModular:=false);
assert #G eq 16;
assert (A+1)*(A+2) in I;
assert (A+1)*(Y+3) in I;
assert (A+1)*(B+4) in I;
Jminus2:=I+ideal<R|A+2>;
GroebnerBasis(Jminus2:GlobalModular:=false);
assert Y+3 in Jminus2;
assert 2*X^2-3 in Jminus2;
Jminus1:=I+ideal<R|A+1>;
GroebnerBasis(Jminus1:GlobalModular:=false);
assert Y*(X+1)-X^2 in Jminus1;
assert B*X-X+2 in Jminus1;
F8:=X^8+121*X^7-1256*X^6+6903*X^5-1161*X^4-48312*X^3-58008*X^2-17520*X+1584;
assert (X+4)*F8 in Jminus1;
print "PASS_EXACT_POSITIVE_CHART2_ALGEBRA";
quit;
'''
out = Path('/tmp/level25_plus_poles_chart2_certificate.m')
out.write_text(source)
print(out)

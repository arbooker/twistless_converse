"""Prepare an exact unit-ideal check on the remaining denominator-zero stratum.

Input is the regenerated original202 pure normalized negative chart1 rows.
No compatibility equation or division by D0 is assumed.
"""
from pathlib import Path
import re

source = Path('/tmp/level25_cusp_aux_minus_even1_rational_pure.m').read_text()
source = source.split('I:=ideal<R|P>;')[0]
assert len(re.findall(r'Append\(~P,(.*?)\);', source)) == 203
source = source.replace('/tmp/level25_cusp_aux_minus_normalized_last.txt',
                        '/tmp/level25_plus_poles_negative1_dzero_input.txt')
source += '''
assert #P eq 203;
assert P[#P] eq t*A*X*Y-1;
D0:=A*(X-Y)+X^3-X^2-X;
P:=P[1..#P-1] cat [t*A*(A+1)*(A+2)*X*Y-1,D0];
I:=ideal<R|P>;G:=GroebnerBasis(I:GlobalModular:=false);
assert G eq [R!1]; assert 1 in I;
print "PASS_NEGATIVE_GENERIC_DZERO_UNIT_IDEAL";
quit;
'''
out = Path('/tmp/level25_plus_poles_negative1_dzero_certificate.m')
out.write_text(source)
print(out)

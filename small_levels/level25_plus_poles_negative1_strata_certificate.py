"""Prepare exact checks for the A=-1,-2 negative first-chart strata.

Regenerate the original negative all439 primitive syzygies, then run
level25_cusp_aux_minus_even_prepare.py 1 pure to prepare the necessary
202 pure rows. This helper reuses those original rows, not a saved GB.
It launches no subprocess and changes no sibling-owned file.
"""
from pathlib import Path
import re

path = Path('/tmp/level25_cusp_aux_minus_even1_rational_pure.m')
original = path.read_text()
source = original.split('I:=ideal<R|P>;')[0]
assert len(re.findall(r'Append\(~P,(.*?)\);', source)) == 203
source = source.replace('/tmp/level25_cusp_aux_minus_normalized_last.txt',
                        '/tmp/level25_plus_poles_negative1_strata_input.txt')
source += '''
assert #P eq 203;
F8:=X^8+121*X^7-1256*X^6+6903*X^5-1161*X^4-48312*X^3-58008*X^2-17520*X+1584;
F4:=5*X^4+5*X^3-312*X^2-228*X+48;
I:=ideal<R|P cat [A+1]>;G:=GroebnerBasis(I:GlobalModular:=false);
assert Y*(X+1)-X^2 in I;
assert F4*F8 in I;
print "PASS_NEGATIVE_A_MINUS_ONE";
I:=ideal<R|P cat [A+2]>;
G:=GroebnerBasis(I:GlobalModular:=false);
assert (X-4)*(2*X^2-3) in I;
assert (X-4)*(Y+3) in I;
J:=I+ideal<R|X-4>;G:=GroebnerBasis(J:GlobalModular:=false);
assert 213*Y^3+4585*Y^2+500*Y+12096 in J;
assert 4585*9^2 gt 213*9^3+500*9+12096;
print "PASS_NEGATIVE_A_MINUS_TWO";
print "PASS_NEGATIVE_EXCEPTIONAL_STRATA";
quit;
'''
out = Path('/tmp/level25_plus_poles_negative1_strata_certificate.m')
out.write_text(source)
print(out)

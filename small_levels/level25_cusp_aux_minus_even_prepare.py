"""Exact termwise Laurent-unit normalization of saved negative-sign charts.

A=ax, B=by, C=cw, X=x², Y=y², W=w². Every exponent parity is checked.
Finite-field output is exploratory only. No subprocesses are launched.
"""
from pathlib import Path
from fractions import Fraction
import re, sys

chart = int(sys.argv[1])
finite = 'finite' in sys.argv
pure = 'pure' in sys.argv
field = 'GF(32003)' if finite else 'Rationals()'
seed = int(next((a[4:] for a in sys.argv if a.startswith('seed')), '0'))
source = Path(f'/tmp/level25_cusp_aux_minus_seed{seed}_chart{chart}.txt')
raw = re.sub(r'\s+', '', source.read_text().replace('\\',''))
names = ['x','y','z','w','a','b','c','v1','t']
outnames = ['u','C','B','A','Z','W','Y','X','t']
polys = set()
for row in raw[1:-1].split(','):
    terms = []
    for sgn, term in re.findall(r'([+-]?)([^+-]+)', row):
        coeff = Fraction(-1 if sgn == '-' else 1)
        exp = [0]*9
        for factor in term.split('*'):
            m = re.fullmatch(r'(x|y|z|w|a|b|c|v1|t)(?:\^(\d+))?', factor)
            if m:
                exp[names.index(m[1])] += int(m[2] or 1)
            else:
                coeff *= Fraction(factor)
        terms.append((coeff, exp))
    if any(e[8] for c,e in terms):
        continue
    shifts = [[e[0]-e[4],e[1]-e[5],e[2],e[3]-e[6]] for c,e in terms]
    mins = [min(e[j] for e in shifts) for j in range(4)]
    transformed = {}
    for (c,e), s in zip(terms,shifts):
        assert all((s[j]-mins[j]) % 2 == 0 for j in range(4)), (row, e)
        d = [(s[j]-mins[j])//2 for j in range(4)]
        ex = (e[7],e[6],e[5],e[4],d[2],d[3],d[1],d[0],0)
        transformed[ex] = transformed.get(ex, Fraction(0)) + c
    transformed = {e:c for e,c in transformed.items() if c}
    if not transformed:
        continue
    if pure and any(e[1] or e[4] or e[5] for e in transformed):
        continue
    # A,X,Y,W are units; divide only their common powers.
    units = {j:min(e[j] for e in transformed) for j in [3,4,5,6,7]}
    transformed = {tuple(v-units.get(j,0) for j,v in enumerate(e)):c for e,c in transformed.items()}
    lead = transformed[max(transformed)]
    termsout = []
    for e,c in sorted(transformed.items()):
        c /= lead
        factors = [str(c)] + [n+(f'^{v}' if v != 1 else '') for n,v in zip(outnames,e) if v]
        termsout.append('*'.join(factors))
    polys.add('+'.join(termsout).replace('+-','-'))
if pure:
    ringnames = ['u','B','A','Y','X','t']
    sat = 't*X*Y*A-1'
else:
    ringnames = outnames
    sat = 't*X*Y*Z*W*A-1'
text = 'Alarm(45); SetMemoryLimit(500000000); SetNthreads(1); SetQuitOnError(true); SetGBGlobalModular(false);\n'
text += f'R<{",".join(ringnames)}>:=PolynomialRing({field},{len(ringnames)},"grevlex");\nP:=[R|];\n'
text += ''.join('Append(~P,'+p+');\n' for p in sorted(polys,key=lambda p:(len(p),p)))
text += f'Append(~P,{sat});\nprint "NORMALIZED_ROWS",#P;\n'
text += 'Write("/tmp/level25_cusp_aux_minus_normalized_last.txt",P : Overwrite:=true);\n'
text += 'I:=ideal<R|P>; time G:=GroebnerBasis(I); print "GB",#G,"DIM",Dimension(I);\n'
text += f'if Dimension(I) eq 0 then print "DEGREE",QuotientDimension(I); print "X_FACTORS",Factorization(UnivariateEliminationIdealGenerator(I,{len(ringnames)-1}));end if;\n'
text += f'Write("/tmp/level25_cusp_aux_minus_even_seed{seed}_chart{chart}_{field.replace("(","").replace(")","")}_gb.txt",G : Overwrite:=true);\n'
text += 'for g in G do if #Monomials(g) le 18 then print g;end if;end for;\nquit;\n'
out = Path(f'/tmp/level25_cusp_aux_minus_even{chart}_{"finite" if finite else "rational"}_{"pure" if pure else "full"}.m')
out.write_text(text)
print(out, 'rows', len(polys), 'bytes',len(text))

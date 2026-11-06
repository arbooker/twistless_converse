"""Exact leading-system tests for a chi3 pole chain whose top point is s=k.
Run ETA BAD3 BAD11. Integer m=k/2>=1, gap n satisfies 0<=n<=m.
The analytic n>=1 factor inequalities are documented in level33_pole_chains.tex.
"""
from pathlib import Path
source=Path(__file__).with_name('level33_first_jet.py').read_text()
exec(source[:source.index('import json')])
from sympy import Matrix,Rational
f=(A+X)*(A+X+1)*(X*yy-bad3*X+yy+bad3)
f=Poly(f,A,X,yy,zz).monic().as_expr()
assert f in leading_polys
# The only possible zero of A+X for n>=1,m>=n is n=m=1.
# Its top leading matrix has rank66 for every sign choice.
point={xx:2,yy:3,zz:11,aa:-2}
M=Matrix([[v.as_expr().subs(point) for v in row] for row in lead])
assert M.rank()==2
# For gap n=0, A=-X-1. A nonzero minor at integer m excludes the pole.
candidates=list(dict.fromkeys(expand(p.subs(A,-X-1)) for p in leading_polys))
candidates=[p for p in candidates if p]
candidates.sort(key=lambda p:(Poly(p,X,yy,zz).total_degree(),len(Poly(p,X,yy,zz).terms())))
certificate=None
for p in candidates:
 terms={4**i*3**j*11**k:Rational(c) for (i,j,k),c in Poly(p,X,yy,zz).terms()}
 top=max(terms);leadcoef=abs(terms[top])
 cutoff=next((m for m in range(2,31) if sum(abs(c)*base**m for base,c in terms.items() if base!=top)<leadcoef*top**m),None)
 if cutoff is None:continue
 small=[sum(c*base**m for base,c in terms.items()) for m in range(2,cutoff)]
 if any(v==0 for v in small):continue
 certificate={'polynomial':str(p),'cutoff':cutoff,'small_values':list(map(str,small)),'largest_base':top}
 break
assert certificate
point={xx:2,yy:3,zz:11,aa:Rational(-5,2)}
rank=Matrix([[v.as_expr().subs(point) for v in row] for row in lead]).rank()
assert rank==(1 if (eta,bad3,bad11)==(-1,1,-1) else 2)
import json
record={'signs':[eta,bad3,bad11],'gap_positive_minor':str(f),'gap_one_weight_two_rank':Q,
        'gap_zero':certificate,'weight_two_rank':len(piv)+rank}
Path('/tmp/level33_weightchain_'+''.join('p' if v==1 else 'm' for v in (eta,bad3,bad11))+'.json').write_text(json.dumps(record,indent=2))
print('N33_WEIGHT_CHAIN_VERIFIED',eta,bad3,bad11,certificate,'rank at m1',len(piv)+rank,flush=True)

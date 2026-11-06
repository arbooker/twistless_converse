"""Exploratory Q84 necessary conditions on coordinate24; not pole exclusion."""
from pathlib import Path
base=Path(__file__).parent
source=(base/'level28_pole_reduction.py').read_text()
source=source.replace("exec(Path(__file__).with_name('level28_jet_builder.py').read_text())",
 "exec((base/'level28_jet_builder.py').read_text().replace('N=28;Q=42','N=28;Q=84'))")
source=source[:source.index("print('free'")]
exec(source)
import sympy as sp
assert free==[24,53]
assert all(not r[1] for r in lead+jet)
Y,Z,A,T=sp.symbols('y z a T')
ps=list(set(r[0].numer.as_expr() for r in lead+jet if r[0]))
print('signs',eta,bad7,'constraints',len(ps),flush=True)
g=sp.groebner(ps+[T*Y*Z-1],A,Z,T,Y,order='grevlex')
q=15-6*eta*bad7
r=12-5*eta*bad7
expected=sp.groebner([Y**2-q,q*A+(q+1)*Y,Z+eta*r,q*r*T+eta*Y],A,Z,T,Y,order='grevlex')
assert list(g)==list(expected)
assert 7**10 < 9**9 and 21**9 < 17**10
print('necessary ideal for nonzero top coordinate24',list(g),flush=True)
print('kernel53 nonzero support',[j for j,c in enumerate(kernels[1]) if c],flush=True)

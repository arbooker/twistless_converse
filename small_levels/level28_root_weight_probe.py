"""Exploratory N28 quotient leading conditions; no weight exclusion claim."""
from pathlib import Path
base=Path(__file__).parent
source=(base/'level28_pole_reduction.py').read_text()
source=source.replace("exec(Path(__file__).with_name('level28_jet_builder.py').read_text())",
 "exec((base/'level28_jet_builder.py').read_text().replace('N=28;Q=42','N=28;Q=84'))")
source=source[:source.index("print('free'")]
exec(source)
import sympy as sp
Y,Z,A,T=sp.symbols('y z a T')
ps=list(set(r[0].numer.as_expr() for r in lead if r[0]))
g=sp.groebner(ps+[T*Y*Z-1],T,A,Z,Y,order='lex')
print('signs',eta,bad7,'leading ideal',list(g),flush=True)
for p in g:
 if not p.has(A,T):print('eliminant',sp.factor(p),flush=True)

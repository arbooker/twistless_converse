"""Exact final N28 weight-two pole cancellation by the odd quarter twist.
Analytic dependencies and the Mellin functional equation are in companion TeX.
"""
from pathlib import Path
import contextlib,io,sys
sys.argv=[sys.argv[0],'-1','-1']
base=Path(__file__).parent
with contextlib.redirect_stdout(io.StringIO()):
    exec((base/'level28_root_weight_probe.py').read_text())
E=sp.Matrix([[2,-1],[-28,16]])
T=sp.Matrix([[1,1],[0,1]])
W=sp.Matrix([[0,-1],[28,0]])
t=sp.Matrix([[1,sp.Rational(-1,12)],[0,1]])
W1008=sp.Matrix([[0,-1],[1008,0]])
assert E*T*W==-sp.Rational(1,3)*t*W1008*t
point={sp.Symbol('x'):2,sp.Symbol('y'):3,sp.Symbol('z'):7,sp.Symbol('a'):sp.Rational(-10,3)}
assert free==[24,53]
residue=kernels[0][21].as_expr().subs(point)
assert residue!=0
assert kernels[1][21]==0
print('QUARTER_TWIST_EXCEPTIONAL_RESIDUE',residue,flush=True)
# The exact H3 row at j=7 is the Hecke equation at r=1/4.
row=next(row for row,lab in original if lab==('H',3,7))
quarter=sp.Symbol('Fquarter');plus=sp.Symbol('Fplus');minus=sp.Symbol('Fminus')
values={7:plus,35:-minus,63:-quarter,21:quarter}
lhs=sum(coefficient.as_expr()*values[j] for j,coefficient in row.items())
yy,aa=sp.symbols('y a')
assert sp.simplify(lhs-(plus-minus-(1+aa/yy+1/yy**2)*quarter))==0
quarter_translation=sp.Matrix([[1,sp.Rational(1,4)],[0,1]])
G4=sp.Matrix([[4,-1],[-28,8]])
quarter_fricke=quarter_translation*sp.Matrix([[0,-1],[112,0]])*quarter_translation.inv()
assert quarter_fricke*W.inv()*G4==4*sp.eye(2)
delta=sp.diag(1,2)
assert delta.inv()*sp.Matrix([[1,sp.Rational(1,2)],[0,1]])*delta==T
assert delta.inv()*sp.Matrix([[1,0],[14,1]])*delta==sp.Matrix([[1,0],[7,1]])
assert delta.inv()*G4*delta==2*sp.Matrix([[2,-1],[-7,4]])
print('CENTER_EXCHANGE_AND_EXACT_HECKE_IDENTITY_VERIFIED',flush=True)

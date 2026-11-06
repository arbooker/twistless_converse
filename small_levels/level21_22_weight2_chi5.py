"""Exact N21 exceptional-weight-two chi5 pole cancellation certificate.

Checks the known center-exchange matrix, the Q210 old-zero determinant,
and a uniform exponential-polynomial obstruction for every nonnegative
integer shift of every possible chi5 pole. See companion .tex for analysis.
This does not claim the full N21 converse or eliminate its old-grid pole.
"""
import sys,json,hashlib
from pathlib import Path
import sympy as sp
base=Path(__file__).parent
# Recompute rather than trust a stored symbolic determinant.
sys.argv=['certificate','21']
exec((base/'level21_22_extra_prime5_poles.py').read_text())
assert N==21 and Q==210 and len(basis)==208
X,Y,U,R,T=sp.symbols('X Y U R T')
P=4*X**4+3*X**3*Y+3*X**3-4*X**2*Y+4*X**2-3*X*Y+3*X-4*Y
expected=-(X**2-1)*P/(3*X**3*Y)
assert sp.cancel(success[2].as_expr().subs({xx:X,yy:Y})-expected)==0
E=sp.Matrix([[2,-1],[-21,11]]);trans=sp.Matrix([[1,1],[0,1]]);W=sp.Matrix([[0,-1],[21,0]])
t=lambda q:sp.Matrix([[1,q],[0,1]])
exchange=t(sp.Rational(-1,10))*sp.Matrix([[0,-1],[2100,0]])*t(sp.Rational(-1,10))
assert E*trans*W==-exchange/10
# u is a possible chi5 denominator root, u+u^-1=3/2.
A=sp.expand(P).coeff(Y);B=sp.expand(P).subs(Y,0)
H=sp.expand(B.subs(X,R*U)*B.subs(X,R*(sp.Rational(3,2)-U))-T**2*A.subs(X,R*U)*A.subs(X,R*(sp.Rational(3,2)-U)))
H=sp.rem(H,2*U**2-3*U+2,U)
assert U not in H.free_symbols
H4=sp.Poly(4*H,R,T)
terms={}
for powers,coefficient in H4.terms():
 exponential_base=2**powers[0]*3**powers[1]
 terms[exponential_base]=terms.get(exponential_base,0)+int(coefficient)
terms={b:c for b,c in terms.items() if c}
assert max(terms)==576 and terms[576]==-36
cutoff=3
margin=36*576**cutoff-sum(abs(c)*b**cutoff for b,c in terms.items() if b!=576)
assert margin==3706333056 and margin>0
small=[sum(c*b**n for b,c in terms.items()) for n in range(cutoff)]
assert small==[54,10656,-2232288]
assert all(small)
print('N21_CHI5_SHIFT_CLASS_EXCLUDED', 'n<3',small,'n>=3 dominance margin',margin,flush=True)
print('H4=',H4.as_expr(),flush=True)
files=['level21_22_weight2_chi5.py','level21_22_extra_prime5_poles.py','level21_22_extra_prime5.py','level21_augmented_builder.py']
manifest={'theorem':'N21 k2 eta,bad3,bad7=(-1,-1,1), lambda2=-3/2: chi5 entire with FE epsilon525^{-h}', 'small_n_values_H4':small,'dominance_cutoff':cutoff,'dominance_margin':margin,'exponential_terms':terms,'sha256':{f:hashlib.sha256((base/f).read_bytes()).hexdigest() for f in files}}
(base/'level21_22_weight2_chi5.json').write_text(json.dumps(manifest,indent=2)+'\n')

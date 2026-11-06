"""N22 exceptional-weight-two chi5 pole cancellation certificate.
Checks full old-zero Q330 rank when x is any nonnegative power of 2,
via exact resultant factors and elementary positive-polynomial bounds.
See companion .tex for the pole-order argument at s=1,2.
"""
import sys,json,hashlib
from pathlib import Path
import sympy as sp
base=Path(__file__).parent
sys.argv=['certificate','22']
exec((base/'level21_22_extra_prime5_poles.py').read_text())
assert N==22 and Q==330 and len(basis)==328
X,Y=sp.symbols('X Y')
# Eliminate the remaining two coordinates. All rational denominators in
# these reduced rows are nonzero monomials in the exponential variables.
for row,lab in R:
 for v in row.values():assert len(v.denom.terms())==1
row0=R[0][0];pol=[]
for row,lab in R[1:]:
 det=row.get(cols[0],K.zero)*row0.get(cols[1],K.zero)-row.get(cols[1],K.zero)*row0.get(cols[0],K.zero)
 if not det:continue
 pp=det.numer
 # b=5^h occurs with a single exponent; removing it is safe, unlike
 # specializing a polynomial having more than one b-exponent.
 assert len({pw[4] for pw,c in pp.terms()})==1
 assert all(pw[2]==pw[3]==0 for pw,c in pp.terms())
 expr=pp.as_expr().subs({bb:1,xx:X,yy:Y});pp2=sp.Poly(expr,X,Y)
 powers=[min(pw[i] for pw,c in pp2.terms()) for i in range(2)]
 normalized=sp.Poly(expr/X**powers[0]/Y**powers[1],X,Y).monic().as_expr()
 if normalized not in pol:pol.append(normalized)
assert len(pol)==9
resultants=[sp.resultant(pol[0],p,Y) for p in pol[1:]]
resultants=[r for r in resultants if r]
assert len(resultants)>=2
g=resultants[0]
for r in resultants[1:]:g=sp.gcd(g,r)
G=sp.Poly(g,X).monic()
quartic=49*X**4-183*X**2+49
positive5=49*X**5+58*X**4+18*X**3+45*X**2+36*X+36
positive12=13024*X**12+15159*X**11+90542*X**10+214759*X**9+211371*X**8+60397*X**7-64811*X**6-75366*X**5-22023*X**4+5004*X**3+4860*X**2+1944*X+324
expected=X**6*(X+1)**4*(49*X**4+36)**2*quartic*positive5*positive12
assert G==sp.Poly(expected,X).monic()
assert quartic.subs(X,1)==-85 and quartic.subs(X,2)==101
# quartic is increasing for X>=2: derivative=2X(98X²-183)>0.
assert 98*4-183>0
assert all(c>0 for pw,c in sp.Poly(positive5,X).terms())
neg=sum(-c for pw,c in sp.Poly(positive12,X).terms() if c<0)
assert neg==162200 and 211371-neg==49171>0
assert all(pw[0]<=6 for pw,c in sp.Poly(positive12,X).terms() if c<0)
# For X>=1, all negative terms are bounded in modulus by 162200 X^6,
# while the positive X^8 term alone dominates them.
E=sp.Matrix([[2,-1],[-22,12]]);trans=sp.Matrix([[1,1],[0,1]]);W=sp.Matrix([[0,-1],[22,0]])
t=lambda q:sp.Matrix([[1,q],[0,1]])
assert E*trans*W==-sp.Rational(1,5)*t(sp.Rational(-1,10))*sp.Matrix([[0,-1],[1100,0]])*t(sp.Rational(-1,10))
print('N22_Q330_OLD_ZERO_RANK_ALL_X_POWERS_OF_TWO_PASS',flush=True)
print('N22_CHI5_ENTIRE_CERTIFICATE_PASS',flush=True)
files=['level21_22_weight2_chi5_22.py','level21_22_extra_prime5_poles.py','level21_22_extra_prime5.py','level22_uniform_continuation.py']
manifest={'theorem':'N22 exceptional k2 parameters: chi5 entire with FE -epsilon550^{-h}','resultant_gcd_factorization':str(sp.factor(G.as_expr())),'old_zero_rank':330,'uniform_lattice':'x=2^n for all integers n>=0 and arbitrary nonzero y,z,b','sha256':{f:hashlib.sha256((base/f).read_bytes()).hexdigest() for f in files}}
(base/'level21_22_weight2_chi5_22.json').write_text(json.dumps(manifest,indent=2)+'\n')

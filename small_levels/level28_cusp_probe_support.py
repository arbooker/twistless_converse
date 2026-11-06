"""Read-only exact Q84 kernel/support and higher direct Taylor-source probe.
Exploratory algebra only: this is not a meromorphic pole-removal certificate.
"""
from pathlib import Path
import contextlib, io
base=Path(__file__).parent
with contextlib.redirect_stdout(io.StringIO()):
    exec((base/'level28_root_probe.py').read_text())
print('free',free,flush=True)
w=kernels[free.index(53)]
assert w==[K(-1 if j in (11,17,25,31) else 1 if j in (53,59,67,73) else 0) for j in range(Q)]
assert all(sum((v*w[j] for j,v in row.items()),K.zero)==0 for row,lab in original)
for row,lab in original:
    if lab[0]=='g':
        _,A,B,C,D,mu,j=lab
        beta=Q*(A*j+B*Q)//(C*j+D*Q)%Q
        assert C==0 or w[beta]==0
    if lab[0]=='F':
        _,q,t=lab;ell=lcm(N,q*q);u=-(Q*Q//ell)//t
        off=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
        assert sum((w[(j+u)%Q] for j in off),K.zero)==0
print('ALL_ORDERS_CONSTANT_ODD_MODE_ANNIHILATION_VERIFIED',eta,bad7,flush=True)
def uniform_nonzero(poly):
    groups={}
    for powers,coefficient in poly.terms():
        groups.setdefault(powers[:3],[]).append(powers[3:])
    return any(len(g)==1 and not any(g[0]) for g in groups.values())
assert len(piv)==82
assert all(row.get(53,K.zero)==0 for row,rid in R)
residuals=[(rid,row[24]) for row,rid in R if row.get(24) and
           uniform_nonzero(row[24].numer) and uniform_nonzero(row[24].denom)]
assert residuals
print('UNIFORM_QUOTIENT_LEADING_RANK_83_VERIFIED',eta,bad7,
      'residual',original[residuals[0][0]][1],str(residuals[0][1]),flush=True)
if 'structural' in sys.argv:
    raise SystemExit(0)
for col,pole in zip(free,kernels):
    print('kernel',col,'support',[j for j,v in enumerate(pole) if v],flush=True)
    if col==53:
        print('odd kernel values',[(j,str(v)) for j,v in enumerate(pole) if v],flush=True)
    for order in range(1,5):
        def nth_rhs(lab):
            if lab[0]=='g':
                _,A,B,C,D,mu,j=lab
                den=C*j+D*Q; beta=Q*(A*j+B*Q)//den%Q; det=A*D-B*C
                return shift(mu*mon(Fraction(den*den,det*Q*Q)),order)*K(Fraction(C*den,det*Q))**order*pole[beta]
            if lab[0]=='F':
                _,q,t=lab; ell=lcm(N,q*q);u=-(Q*Q//ell)//t
                leading=eta*(-bad7 if q%7==0 else 1)*mon(Fraction(ell*t*t,Q*Q))
                off=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
                return shift(leading,order)*K(Fraction(ell*t,Q))**order*sum((pole[(j+u)%Q] for j in off),K.zero)
            return K.zero
        vec=[nth_rhs(lab) for row,lab in original]
        raw_nonzero=sum(bool(v) for v in vec)
        for rid,val,updates in operations:
            vec[rid]/=shift(val,order)
            for rid2,coef in updates:vec[rid2]-=shift(coef,order)*vec[rid]
        nonzero=[rid for rid in zeroids if vec[rid]]
        print('order',order,'raw nonzero',raw_nonzero,'zero-row nonzero',len(nonzero),
              'sample',[(original[rid][1],str(vec[rid])) for rid in nonzero[:2]],flush=True)
        if col==53:
            solution=[K.zero]*Q
            for j,row,rid in reversed(piv):
                solution[j]=vec[rid]-sum((shift(v,order)*solution[c] for c,v in row.items() if c!=j),K.zero)
            print('particular support',[(j,str(v)) for j,v in enumerate(solution) if v],flush=True)

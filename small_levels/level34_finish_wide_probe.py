"""Finite-field reconnaissance only; NO meromorphic-continuation certificate.
Checks generic leading nullspace support and complete-support closure on wider grids.
"""
import sys
from pathlib import Path
cutoff = int(sys.argv[4]) if len(sys.argv) > 4 else 204
src = Path(__file__).with_name('level34_jet_builder.py').read_text()
exec(src.replace('N=34;Q=102', 'N=34;Q='+str(cutoff)))
prime = 1009
point = [2,3,17,5,7]
def polyeval(p):
    ans = 0
    for exps, cf in p.terms():
        c = int(cf.numerator) * pow(int(cf.denominator), -1, prime) % prime
        for v, e in zip(point, exps):
            c = c * pow(v, e, prime) % prime
        ans = (ans+c) % prime
    return ans
def ev(v): return polyeval(v.numer)*pow(polyeval(v.denom),-1,prime)%prime
def elim(rows, cols):
    basis = {}
    for row, lab in rows:
        r = {j:ev(v) for j,v in row.items() if ev(v)}
        while r:
            j = min(r)
            if j not in basis:
                iv = pow(r[j],-1,prime); basis[j]={c:v*iv%prime for c,v in r.items()};break
            b = basis[j]; c = r[j]
            for k,v in b.items():
                r[k]=(r.get(k,0)-c*v)%prime
                if not r[k]:del r[k]
    free = sorted(set(cols)-set(basis)); support=set()
    for j in free:
        v={j:1}
        for k,b in sorted(basis.items(),reverse=True):
            c=-sum(u*v.get(l,0) for l,u in b.items() if l!=k)%prime
            if c:v[k]=c
        support|=set(v)
    return len(basis), free, support
rank,free,support=elim(R,range(Q))
print('generic full rank',rank,'free',free,'nullsupport',sorted(support),flush=True)
U=set(range(Q))-support
def closed(row,lab):
    if not set(row)<=U:return False
    if lab[0]=='g':
        _,A,B,C,D,mu,j=lab;den=C*j+D*Q
        return j in U and (Q*(A*j+B*Q)//den)%Q in U
    if lab[0]=='F':
        _,q,t=lab;ell=lcm(N,q*q);u=-(Q*Q//ell)//t
        off=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
        return all((j+t)%Q in U and (j+u)%Q in U for j in off)
    return True
closedrows=[(r,l) for r,l in R if closed(r,l)]
rank2,free2,support2=elim(closedrows,U)
print('closed U',len(U),'rank',rank2,'free',free2,'rows',len(closedrows),flush=True)
print('denominators contained',[q for q in divisors(Q) if all(j in U for j in range(0,Q,Q//q))],flush=True)
import json
Path('/tmp/level34_finish_grid_'+str(Q)+'.json').write_text(json.dumps({'Q':Q,'U':sorted(U),'rank':rank2,'rows':len(closedrows),'claim':'Finite-field reconnaissance only'},indent=2))

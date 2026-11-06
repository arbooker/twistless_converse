"""Exact N34 closed 168-coordinate subsystem of the 204-grid.

The omitted coordinates were located by finite-field reconnaissance; all
claims subsequently require the independent exact symbolic rank verifier.
Complete Taylor support is checked before any row is retained.
"""
from pathlib import Path
src = Path(__file__).with_name('level34_jet_builder.py').read_text()
exec(src.replace('N=34;Q=102', 'N=34;Q=204'))
excluded = {19,22,23,25,43,46,49,53,56,59,62,65,71,74,77,80,83,91,
            113,121,124,127,130,133,139,142,145,148,151,155,158,161,179,181,182,185}
U = set(range(Q)) - excluded
def closed(row, lab):
    if not set(row) <= U:
        return False
    if lab[0] == 'g':
        _, A, B, C, D, mu, j = lab; den = C*j+D*Q
        return j in U and (Q*(A*j+B*Q)//den) % Q in U
    if lab[0] == 'F':
        _, q, t = lab; ell = lcm(N,q*q); u = -(Q*Q//ell)//t
        off = [a0*(Q//q) for a0 in range(q) if gcd(a0,q) == 1]
        return all((j+t) % Q in U and (j+u) % Q in U for j in off)
    return True
R = [(r,lab) for r,lab in R if closed(r,lab)]
assert len(U) == 168
assert all(j in U for q in [3,4,12,34] for j in range(0,Q,Q//q))
print('closed wide',len(U),'rows',len(R),flush=True)

"""Exact grid relations on a closed support located by finite-field scouting.
This checks closure, but does not itself prove meromorphic continuation.
"""
from pathlib import Path
import sys,json
qarg=next(v for v in sys.argv if v.startswith('grid'))
qtarget=int(qarg[4:]);recon=json.loads(Path('/tmp/level34_finish_grid_'+str(qtarget)+'.json').read_text())
src=Path(__file__).with_name('level34_jet_builder.py').read_text()
exec(src.replace('N=34;Q=102','N=34;Q='+str(qtarget)))
U=set(recon['U'])
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
R=[(r,l) for r,l in R if closed(r,l)]
print('exact closed grid',Q,'size',len(U),'rows',len(R),flush=True)
assert all(j in U for q in [3,34] for j in range(0,Q,Q//q))

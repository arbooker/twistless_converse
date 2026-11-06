"""Exact N25 rows enlarged by words involving the known Fricke involution.
Every included word has a tracked eigenvalue; no modularity is presumed.
"""
from pathlib import Path
import sys
from functools import reduce
from math import gcd
def known_aug(N,depth):
 def norm(g):
  d=reduce(gcd,g);g=tuple(v//d for v in g)
  return tuple(-v for v in g) if next(v for v in g if v)<0 else g
 def mm(g,h):
  a,b,c,d=g;e,f,q,r=h
  return norm((a*e+b*q,a*f+b*r,c*e+d*q,c*f+d*r))
 def ii(g):a,b,c,d=g;return norm((d,-b,-c,a))
 gen=[((1,1,0,1),1),((1,0,25,1),1),((2,-1,-25,13),1),((0,-1,25,0),eta)]
 gen += [(ii(g),mu) for g,mu in gen]
 old={((1,0,0,1),1)};front=old
 for _ in range(depth):
  nxt={(mm(g,h),mu*nu) for g,mu in front for h,nu in gen}-old
  old|=nxt;front=nxt
 return old
src=Path(__file__).with_name('level25_uniform_continuation.py').read_text()
src=src[:src.index("print('rows'")]
if 'Q300' in sys.argv:src=src.replace('N=25;Q=150','N=25;Q=300')
src=src.replace('for A,B,C,D in known(N,3):','for (A,B,C,D),mu in known_aug(N,3):')
src=src.replace('c=mon(Fraction(den,Q))**2','c=mu*mon(Fraction(den*den,(A*D-B*C)*Q*Q))')
src=src.replace("('g',A,B,C,D,j)","('g',A,B,C,D,mu,j)")
exec(src)

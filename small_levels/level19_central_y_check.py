from pathlib import Path
import sys,sympy as sp
src=Path('small_levels/level19_pole_probe.py').read_text();exec(src[src.index('import sys,time'):src.index('pivs,jrows=elim(jet,Q)')])
pivs,rem=elim(original,Q)
assert len(pivs)==111
checked_target=False
R=K.ring
xx,yy,zz,aa,bb=sp.symbols('x y z a b')
ans=[]
for rr,ll in rem:
 f=rr.get(18,K.zero)
 if not f:continue
 p=sp.Poly(f.numer.as_expr().subs(aa,-xx-1/xx).expand()*xx**20,yy)
 g=sp.rem(p,sp.Poly(yy**2+1,yy)).as_expr().expand()
 if ll == ('H',3,5):
  assert sp.expand(g+xx**22)==0
  checked_target=True
 if g:
  st=str(sp.factor(g))
  if st not in ans:ans.append(st);print('NONZERO',ll,st,flush=True)
print('COUNT',len(ans))
assert checked_target, 'The required monomial row must be checked'
print('PASS: the H3 row has nonzero monomial numerator -x**22')

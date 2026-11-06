"""Export literal quotient leading/first-Taylor rows to bounded Magma."""
from pathlib import Path
import sys
base=Path(__file__).parent
src=(base/'level25_cusp_aux_prime7_symbolic.py').read_text();cut=src.index("\nif 'old150' in sys.argv:\n    assert not R")
sys.argv.append('old150');exec(src[:cut]);assert not R
gauges=list(free);original=[(row,lab) for row,lab in original if lab[0]!='old150'];original += [({j:K.one},('gauge',j)) for j in gauges]
text='Alarm(150); SetSeed(1);\nK<x,y,z,w,a,b,c>:=RationalFunctionField(Rationals(),7);\n'
text+='Q:=1050; nonzero2:='+('true' if 'nonzero2' in sys.argv else 'false')+';\nA:=[* *];J:=[* *];\n'
def emit(row,name):
 result='rr:=AssociativeArray(Integers());\n'
 for j,v in row.items():
  if v:result+='rr[%d]:=%s;\n'%(j+1,str(v.as_expr()).replace('**','^').replace('lam7','c'))
 return result+'Append(~'+name+',rr);\n'
for row,lab in original:
 text+=emit(row,'A');source={}
 if lab[0]=='g':
  _,A,B,C,D,mu,j=lab;den=C*j+D*Q;dest=Q*(A*j+B*Q)//den%Q
  source[dest]=mu*mon(Fraction(den*den,(A*D-B*C)*Q*Q))*K(Fraction(C*Q,den))
 if lab[0]=='F':
  _,q,t=lab;ell=lcm(N,q*q);u=-(Q*Q//ell)//t
  coeff=eta*mon(Fraction(ell*t*t,Q*Q))*K(Fraction(Q,t))
  source={(j*(Q//q)+u)%Q:coeff for j in range(q) if gcd(j,q)==1}
 text+=emit(source,'J')
text+=(base/'level25_cusp_aux_magma_firstjet_backend.m').read_text()
suffix='_nonzero2' if 'nonzero2' in sys.argv else ('_zero2' if 'zero2' in sys.argv else '')
out=Path('/tmp/level25_cusp_aux_magma_firstjet_'+str(eta)+suffix+'.m');out.write_text(text);print('EXPORTED',out,len(text),flush=True)

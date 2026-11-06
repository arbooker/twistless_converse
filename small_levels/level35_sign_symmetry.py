"""Exact sign covariance of all level-35 leading and Taylor rows.

The flips (eta,sigma5,z)->(-eta,-sigma5,-z) and the analogous
7-flip preserve the system. Thus the eight sign cases have two classes,
indexed by eta*sigma5*sigma7. No pole-removal claim follows by itself.
"""
from pathlib import Path
import sys,json,hashlib
from fractions import Fraction
SRC=Path(__file__).with_name('level35_full_continuation.py')
source=SRC.read_text().split('def audit(poly):')[0]

def system(eta,bad5,bad7):
 old=sys.argv;sys.argv=[str(SRC),str(eta),str(bad5),str(bad7)]
 ns={};exec(source,ns);sys.argv=old
 K=ns['K'];Q=ns['Q'];N=ns['N'];mon=ns['mon']
 def transform(f):
  def pol(p):
   return K(p.ring.from_dict({pw:cf*((-bad5)**pw[2])*((-bad7)**pw[3]) for pw,cf in p.terms()}))
  return pol(f.numer)/pol(f.denom)
 def shift(f):
  def pol(p):
   return K(p.ring.from_dict({pw:cf/(ns['QQ'](2)**pw[0]*ns['QQ'](3)**pw[1]*ns['QQ'](5)**pw[2]*ns['QQ'](7)**pw[3]) for pw,cf in p.terms()}))
  return pol(f.numer)/pol(f.denom)
 def first(ll):
  if ll[0]=='g':
   _,A,B,C,D,mu,j=ll;den=C*j+D*Q;idx=Q*(A*j+B*Q)//den%Q;det=A*D-B*C
   return {idx:shift(mu*mon(Fraction(den*den,det*Q*Q)))*K(Fraction(C*den,det*Q))}
  if ll[0]=='F':
   _,q,t=ll;ell=ns['lcm'](N,q*q);u=-(Q*Q//ell)//t
   off=[aa*(Q//q) for aa in range(q) if ns['gcd'](aa,q)==1]
   lead=eta*(-bad5 if q%5==0 else 1)*(-bad7 if q%7==0 else 1)*mon(Fraction(ell*t*t,Q*Q))
   return {(aa+u)%Q:shift(lead)*K(Fraction(ell*t,Q)) for aa in off}
  return {}
 out={}
 for rr,ll in ns['R']:
  key=ll[:5]+ll[6:] if ll[0]=='g' else ll
  lead=tuple((j,str(transform(v))) for j,v in sorted(rr.items()) if v)
  jet=tuple((j,str(transform(v))) for j,v in sorted(first(ll).items()) if v)
  assert key not in out
  out[key]=(lead,jet)
 return out

if __name__=='__main__':
 refs={c:system(c,-1,-1) for c in [-1,1]};report=[]
 for eta in [-1,1]:
  for bad5 in [-1,1]:
   for bad7 in [-1,1]:
    rows=system(eta,bad5,bad7);assert rows==refs[eta*bad5*bad7]
    report.append({'eta':eta,'sigma5':bad5,'sigma7':bad7,'class':eta*bad5*bad7,'rows':len(rows),'leading_and_first_taylor_covariance':True})
    print('PASS',eta,bad5,bad7,'class',eta*bad5*bad7,'rows',len(rows),flush=True)
 out={'source_sha256':hashlib.sha256(SRC.read_bytes()).hexdigest(),'checks':report}
 Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')

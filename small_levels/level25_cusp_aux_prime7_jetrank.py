"""Reduce saved genuine leading/first-jet constraints by uniform safe pivots."""
import sys,json,time
from pathlib import Path
from sympy.polys.fields import field
from sympy import QQ,factor
jet_prefix='level25_cusp_aux_oldgerm_' if 'old' in sys.argv else 'level25_cusp_aux_prime7_firstjet_';eta=int(sys.argv[1]);jet_suffix='_zero2' if 'zero2' in sys.argv else ('_nonzero2' if 'nonzero2' in sys.argv else '');data=json.loads(Path('/tmp/'+jet_prefix+str(eta)+jet_suffix+'.json').read_text())
K,x,y,z,w,a,b,c=field('x,y,z,w,a,b,c',QQ)
def decode(v):
 return K(K.ring.from_dict({tuple(p):QQ(q) for p,q in v['num']}))/K(K.ring.from_dict({tuple(p):QQ(q) for p,q in v['den']}))
R=[({int(i):decode(v) for i,v in item['row'].items()},item['lab']) for item in data['rows']]
unit_count=5 if 'nonzero2' in sys.argv else 4
def safe(v):return len(v.numer.terms())==len(v.denom.terms())==1 and not any(v.numer.terms()[0][0][unit_count:]) and not any(v.denom.terms()[0][0][unit_count:])
piv=[];start=time.monotonic()
while R:
 chosen=None
 for i,(row,lab) in enumerate(R):
  if (chosen is None or len(row)<len(R[chosen][0])) and any(safe(v) for v in row.values()):chosen=i
 if chosen is None:break
 row,lab=R.pop(chosen);col=min((j for j,v in row.items() if safe(v)),key=lambda j:sum(j in rr for rr,ll in R));val=row[col];row={j:v/val for j,v in row.items()};piv.append((col,row,lab));new=[]
 for rr,ll in R:
  if col in rr:
   co=rr[col]
   for j,v in row.items():
    rr[j]=rr.get(j,K.zero)-co*v
    if not rr[j]:del rr[j]
  if rr:new.append((rr,ll))
 R=new
 if time.monotonic()-start>90:raise TimeoutError
free=sorted(set(range(len(data['free'])))-{j for j,row,lab in piv})
print('JET_RANK',len(piv),'OF',len(data['free']),'REMAINING',free,'ROWS',len(R),flush=True)
normalized={}
for row,lab in R:
 terms=[]
 for j,v in row.items():
  assert len(v.denom.terms())==1
  dp,dc=v.denom.terms()[0];assert not any(dp[unit_count:])
  terms += [(j,tuple(p[i]-dp[i] for i in range(7)),q/dc) for p,q in v.numer.terms()]
 mins=[min(p[i] for j,p,q in terms) for i in range(unit_count)]+[0]*(7-unit_count)
 shifted=sorted((j,tuple(p[i]-mins[i] for i in range(7)),q) for j,p,q in terms)
 scalar=shifted[0][2];canonical=tuple((j,p,str(q/scalar)) for j,p,q in shifted)
 normalized.setdefault(canonical,lab)
output={'eta':eta,'free':free,'rows':[{'lab':lab,'terms':[(j,list(p),q) for j,p,q in row]} for row,lab in normalized.items()]}
Path('/tmp/'+jet_prefix+'reduced_'+str(eta)+jet_suffix+'.json').write_text(json.dumps(output))
print('UNIQUE',len(normalized),flush=True)
for row,lab in sorted(normalized.items(),key=lambda t:len(t[0]))[:8]:
 print('SHORT',lab,{j:str(factor(sum((K.from_expr(__import__('sympy').Rational(q))*x**p[0]*y**p[1]*z**p[2]*w**p[3]*a**p[4]*b**p[5]*c**p[6] for i,p,q in row if i==j),K.zero).as_expr())) for j in free},flush=True)

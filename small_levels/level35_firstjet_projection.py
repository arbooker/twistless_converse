"""Exploratory exact firstjet residue reduction on the full level35 grid.
Division only by nonzero Laurent monomials in prime powers; no theorem claim.
"""
from pathlib import Path
exec(Path(__file__).with_name('level35_full_continuation.py').read_text().split('def audit(poly):')[0])
original=[(dict(rr),ll) for rr,ll in R]
def shift(f):
 def pol(poly):return K(poly.ring.from_dict({pw:cf/(QQ(2)**pw[0]*QQ(3)**pw[1]*QQ(5)**pw[2]*QQ(7)**pw[3]) for pw,cf in poly.terms()}))
 return pol(f.numer)/pol(f.denom)
def unit(v):return len(v.numer.terms())==len(v.denom.terms())==1 and not any(v.numer.terms()[0][0][4:]) and not any(v.denom.terms()[0][0][4:])
def first(ll):
 if ll[0]=='g':
  _,A,B,C,D,mu,j=ll;den=C*j+D*Q;idx=Q*(A*j+B*Q)//den%Q;det=A*D-B*C
  return {Q+idx:shift(mu*mon(Fraction(den*den,det*Q*Q)))*K(Fraction(C*den,det*Q))}
 if ll[0]=='F':
  _,q,t=ll;ell=lcm(N,q*q);u=-(Q*Q//ell)//t
  off=[aa*(Q//q) for aa in range(q) if gcd(aa,q)==1]
  lead=eta*(-bad5 if q%5==0 else 1)*(-bad7 if q%7==0 else 1)*mon(Fraction(ell*t*t,Q*Q))
  return {Q+(aa+u)%Q:shift(lead)*K(Fraction(ell*t,Q)) for aa in off}
 return {}
def eliminate(rows,bound):
 piv=[];start=time.time()
 while rows:
  cand=[i for i,(rr,ll) in enumerate(rows) if any(j<bound and unit(v) for j,v in rr.items())]
  if not cand:break
  ii=min(cand,key=lambda i:(sum(j<bound for j in rows[i][0]),len(rows[i][0])))
  rr,ll=rows.pop(ii);j=min((j for j,v in rr.items() if j<bound and unit(v)),key=lambda j:sum(j in rr for rr,l in rows));val=rr[j];rr={c:v/val for c,v in rr.items()};piv.append((j,rr));new=[]
  for row,lab in rows:
   if j in row:
    v=row[j]
    for c,u in rr.items():
     row[c]=row.get(c,K.zero)-v*u
     if not row[c]:row.pop(c)
   if row:new.append((row,lab))
  rows=new
  if len(piv)%40==0:print('pivots',len(piv),'rows',len(rows),'sec',round(time.time()-start,1),flush=True)
  if time.time()-start>300:raise TimeoutError
 return piv,rows
jet=[]
for rr,ll in original:
 row={j:shift(v) for j,v in rr.items()};row.update(first(ll));row={j:v for j,v in row.items() if v};jet.append((row,ll))
lp,left=eliminate(jet,Q)
syzygies=[({j-Q:v for j,v in r.items()},l) for r,l in left if all(j>=Q for j in r)]
left=[(r,l) for r,l in left if any(j<Q for j in r)]
print('lower free',Q-len(lp),'remaining',len(left),'syzygies',len(syzygies),flush=True)
# Exact proportional-row cancellation, without division.
extra=[];groups={}
for r,l in left:
 ar={j:v for j,v in r.items() if j<Q};j=min(ar);av=ar[j]
 key=tuple((c,str(v/av)) for c,v in sorted(ar.items()))
 if key not in groups:groups[key]=(r,l,av);continue
 ss,ll,bv=groups[key]
 out={c-Q:r.get(c,K.zero)*bv-ss.get(c,K.zero)*av for c in set(r)|set(ss) if c>=Q};out={j:v for j,v in out.items() if v}
 if out:extra.append((out,('pair',l,ll)))
print('proportional syzygies',len(extra),flush=True)
syzygies+=extra
piv,result=eliminate([(dict(rr),ll) for rr,ll in original]+syzygies,Q)
cols=sorted({j for rr,ll in result for j in rr});print('top free',Q-len(piv),'cols',cols,'rows',len(result),flush=True)
target={70:K.one,140:-K.one}
for j,row in piv:
 if j in target:
  v=target[j]
  for c,u in row.items():
   target[c]=target.get(c,K.zero)-v*u
   if not target[c]:target.pop(c)
print('chi3 target',target,flush=True)
out={'target':{str(j):str(v) for j,v in target.items()},'eta':eta,'bad5':bad5,'bad7':bad7,'columns':cols,'rows':[{str(j):str(v) for j,v in rr.items()} for rr,ll in result]}
Path('/tmp/level35_firstjet_reduced.json').write_text(json.dumps(out))

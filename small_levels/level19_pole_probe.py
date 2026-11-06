"""Exploratory exact pole obstruction for N=19 on the 1/114 grid.

Arguments ETA BAD GAP; currently ETA=BAD=-1 is required and GAP is nonnegative.
Creates a Magma input in /tmp; it does not execute Magma or request permissions.
For ETA=BAD=-1 and GAP=0,1 the exported ideal was verified to be the
unit ideal over Q. This is NOT a proof of pole cancellation for N=19:
it treats only fixed gaps, a_2 nonzero, x^4 != 1, y^2 != -1, and
rightmost pole s_0 != k. The remaining gaps and strata remain open.

Variables: x=2^(s_0-k/2), y=3^(s_0-k/2), z=19^(s_0-k/2),
a=sqrt(2)f_2, b=sqrt(3)f_3. GAP=n imposes
 a=-(x/2^n+2^n/x), necessary if a chi_5 pole lies n steps below s_0.
See level19_pole_probe.tex for the meaning of the exact identities.
"""
import sys,time
def divisors(n):
 return [d for d in range(1,n+1) if n%d==0]
def canon(g):
 return tuple(-v for v in g) if next(v for v in g if v)<0 else g
def mul(g,h):
 a,b,c,d=g;e,f,q,r=h
 return canon((a*e+b*q,a*f+b*r,c*e+d*q,c*f+d*r))
def inv(g):
 a,b,c,d=g;return canon((d,-b,-c,a))
def known(N,depth):
 assert N==19
 gen=[(1,1,0,1),(1,0,19,1),(2,-1,-19,10)]
 gen+=list(map(inv,gen));old={(1,0,0,1)};front=old
 for _ in range(depth):
  nxt={mul(g,h) for g in front for h in gen}-old
  old|=nxt;front=nxt
 return old
from math import gcd,lcm
from fractions import Fraction
from sympy.polys.fields import field
from sympy import QQ
K,x,y,z,a,b=field('x,y,z,a,b',QQ)
N=19;Q=114
eta=int(sys.argv[1]) if len(sys.argv)>1 else -1
bad=int(sys.argv[2]) if len(sys.argv)>2 else -1
zero2=len(sys.argv)>3 and sys.argv[3]=='zero2'
if zero2:a=K.zero
V={2:x,3:y,19:z}
def mon(t):
 t=Fraction(t);num=abs(t.numerator);den=t.denominator;r=K.one
 for p,v in V.items():
  while num%p==0:num//=p;r*=v
  while den%p==0:den//=p;r/=v
 assert num==den==1,(t,num,den)
 return r
R=[]
def add(rr,label):
 rr={j:K(v) for j,v in rr.items() if v}
 if rr:R.append((rr,label))
for A,B,C,D in known(N,3):
 for j in range(Q):
  den=C*j+D*Q
  if not den:add({j:1},('ginf',A,B,C,D,j));continue
  num=A*j+B*Q
  if Q*num%den:continue
  v=Q*num//den%Q;c=mon(Fraction(den,Q))**2
  rr={j:K.one};rr[v]=rr.get(v,K.zero)-c;add(rr,('g',A,B,C,D,j))
for q in divisors(Q):
 ell=lcm(N,q*q)
 if Q*Q%ell:continue
 offsets=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
 add({j:1 for j in offsets},('R',q))
 d=Q*Q//ell
 for t0 in divisors(d):
  for t in [t0,-t0]:
   u=-d//t;c=mon(Fraction(ell*t*t,Q*Q))*(-eta)*(-bad if q%19==0 else 1)
   rr={}
   for j in offsets:
    j1=(j+t)%Q;j2=(j+u)%Q;rr[j1]=rr.get(j1,K.zero)+1;rr[j2]=rr.get(j2,K.zero)+c
   add(rr,('F',q,t))
for p,ap in [(2,a),(3,b),(19,K(bad))]:
 for j in range(Q//p):
  rr={j+t*(Q//p):K.one for t in range(p)}
  for col,val in [(p*j%Q,-ap/V[p]),(p*p*j%Q,K.zero if p==19 else V[p]**-2)]:rr[col]=rr.get(col,K.zero)+val
  add(rr,('H',p,j))
original=[(dict(rr),ll) for rr,ll in R]
def shift(f):
 def pol(poly):
  return K(poly.ring.from_dict({pw:cf/(QQ(2)**pw[0]*QQ(3)**pw[1]*QQ(19)**pw[2]) for pw,cf in poly.terms()}))
 return pol(f.numer)/pol(f.denom)
def isunit(v):
 return len(v.numer.terms())==len(v.denom.terms())==1 and v.numer.terms()[0][0][-1]==v.denom.terms()[0][0][-1]==0

def first(ll):
 typ=ll[0]
 if typ=='g':
  _,A,B,C,D,j=ll;den=C*j+D*Q;idx=(Q*(A*j+B*Q)//den)%Q
  return {Q+idx:shift(mon(Fraction(den,Q))**2)*K(Fraction(C*den,Q))}
 if typ=='F':
  _,q,t=ll;ell=lcm(N,q*q);u=-(Q*Q//ell)//t
  offsets=[aa*(Q//q) for aa in range(q) if gcd(aa,q)==1]
  lead=mon(Fraction(ell*t*t,Q*Q))*eta*(-bad if q%19==0 else 1)
  return {Q+(aa+u)%Q:shift(lead)*K(Fraction(ell*t,Q)) for aa in offsets}
 return {}

jet=[]
for rr,ll in original:
 row={j:shift(v) for j,v in rr.items()};row.update(first(ll));row={j:v for j,v in row.items() if v}
 jet.append((row,ll))

def elim(rows,leftbound):
 piv=[];start=time.time()
 while rows:
  cand=[i for i,(rr,ll) in enumerate(rows) if any(j<leftbound and isunit(v) for j,v in rr.items())]
  if not cand:break
  ii=min(cand,key=lambda i:(sum(j<leftbound for j in rows[i][0]),len(rows[i][0])))
  rr,ll=rows.pop(ii);js=[j for j,v in rr.items() if j<leftbound and isunit(v)]
  j=min(js,key=lambda j:sum(j in rr for rr,lll in rows));val=rr[j]
  rr={c:v/val for c,v in rr.items()};piv.append(j)
  new=[]
  for r,l in rows:
   if j in r:
    v=r[j]
    for c,u in rr.items():
     r[c]=r.get(c,K.zero)-v*u
     if not r[c]:del r[c]
   if r:new.append((r,l))
  rows=new
  if len(piv)%20==0:print('PIV',len(piv),'secs',round(time.time()-start,1),flush=True)
  if time.time()-start>90:print('RESOURCE STOP');break
 return piv,rows
pivs,jrows=elim(jet,Q)
syzygies=[({j-Q:v for j,v in r.items()},l) for r,l in jrows if all(j>=Q for j in r)]
left=[(r,l) for r,l in jrows if any(j<Q for j in r)]
extra=[]
for ii,(r,l) in enumerate(left):
 aleft={j:v for j,v in r.items() if j<Q}
 for ss,ll in left[ii+1:]:
  bleft={j:v for j,v in ss.items() if j<Q}
  if set(aleft)!=set(bleft):continue
  j=min(aleft);av=aleft[j];bv=bleft[j]
  if any(v*bv!=bleft[c]*av for c,v in aleft.items()):continue
  out={}
  for c in (set(r)|set(ss)):
   if c<Q:continue
   val=r.get(c,K.zero)*bv-ss.get(c,K.zero)*av
   if val:out[c-Q]=val
  if out:extra.append((out,('pair',l,ll)))
print('PROPORTIONAL SYZYGIES',len(extra),flush=True)
syzygies+=extra
pivs,result=elim([(dict(rr),ll) for rr,ll in original]+syzygies,Q)
print('COMBINED UNIT RANK',len(pivs),'REMAINING',len(result),'COLS',sorted({j for rr,ll in result for j in rr}),flush=True)
import sympy as sp
n=int(sys.argv[3]) if len(sys.argv)>3 else 0
assert eta==bad==-1 and n>=0, 'Only the audited sign stratum and nonnegative gaps are implemented'
assert {j for rr,ll in result for j in rr}=={18,42,72}
scale=QQ(2)**n
aval=-x/scale-scale/x

def composea(f):
 def pol(p):
  out=K.zero
  for pw,cf in p.terms():
   out+=K(cf)*x**pw[0]*y**pw[1]*z**pw[2]*aval**pw[3]*b**pw[4]
  return out
 return pol(f.numer)/pol(f.denom)
J=x**4+(a*a-2)*x*x+1
coefw=-J/(x*a*(y*y+1))
seen=set();polys=[]
for rr,ll in result:
 val=rr.get(18,K.zero)*coefw+rr.get(42,K.zero)-rr.get(72,K.zero)
 if val:
  val=composea(val);num=val.numer.monic();st=str(num)
  if val and st not in seen:
   seen.add(st);polys.append(num)
   pass
with open('/tmp/level19_pole_probe_gap%d_eta%d_bad%d.m'%(n,eta,bad),'w') as f:
 f.write('SetSeed(1);\nR<x,y,z,b,t>:=PolynomialRing(Rationals(),5,"grevlex");\n')
 f.write('P:=['+',\n'.join(str(p).replace('**','^') for p in polys)+'];\n')
 f.write('Append(~P,t*x*y*z*(y^2+1)*(x^4-1)*(x^2+%d)-1);\ntime G:=GroebnerBasis(ideal<R|P>);\nprint "basis size",#G;\nif #G lt 20 then G; end if;\nquit;\n'%(2**(2*n)))
print('COUNT POLYS',len(polys))

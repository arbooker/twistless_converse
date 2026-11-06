"""Exact conditional leading-kernel certificate for the weight-2 exceptions.

Usage: python3 level21_22_extra_prime5.py 21 (or 22).
Also proves meromorphic continuation on Q210/Q330 for every lambda5,
under the specified exceptional signs and lambda2/lambda3. It does NOT
prove that s=2 is rightmost on the enlarged grid; therefore the leading
kernel constraint is not an unconditional residue exclusion.
"""
from pathlib import Path
import sys,time
N=int(sys.argv[1]);oldQ=42 if N==21 else 66;Qnew=oldQ*5
file='level21_augmented_builder.py' if N==21 else 'level22_uniform_continuation.py'
assert N in (21,22)
src=Path(__file__).with_name(file).read_text().replace('Q='+str(oldQ),'Q='+str(Qnew)).replace('V={2:x,3:y,7:z}','V={2:x,3:y,7:z,5:b}').replace('V={2:x,3:y,11:z}','V={2:x,3:y,11:z,5:b}')
if N==22:src=src[:src.index('piv=[];start=time.time()')]
sys.argv=['x','-1','-1','1'];exec(src)
original=[(dict(row),lab) for row,lab in R]
from sympy import symbols,Rational,QQ,factor,Poly,gcd as pgcd
from sympy.polys.fields import field
xx,yy,zz,aa,bb=symbols('x y z a b');point={xx:2,yy:3,zz:(7 if N==21 else 11),aa:Rational(-3,2) if N==21 else Rational(-7,3),bb:5}
KK,t=field('t',QQ)
rows=[]
for row,l in R:
 rr={j:KK(v.as_expr().subs(point)) for j,v in row.items()};rr={j:v for j,v in rr.items() if v}
 rows.append((rr,l))
for j in range(Q//5):
 rr={j+k*(Q//5):KK.one for k in range(5)}
 for col,v in [(5*j%Q,-t/5),(25*j%Q,KK(1)/25)]:rr[col]=rr.get(col,KK.zero)+v
 rows.append((rr,('H',5,j)))
R=rows;basis=[];st=time.time()
def safe(v):return v.numer.degree()==v.denom.degree()==0
while R:
 choices=[i for i,(r,l) in enumerate(R) if any(safe(v) for v in r.values())]
 if not choices:break
 ii=min(choices,key=lambda i:len(R[i][0]));row,lab=R.pop(ii)
 j=min((j for j,v in row.items() if safe(v)),key=lambda j:sum(j in rr for rr,ll in R))
 val=row[j];row={i:v/val for i,v in row.items()};basis.append((j,row,lab));new=[]
 for rr,ll in R:
  if j in rr:
   c=rr[j]
   for i,v in row.items():
    rr[i]=rr.get(i,KK.zero)-c*v
    if not rr[i]:del rr[i]
  if rr:new.append((rr,ll))
 R=new
 if time.time()-st>45:raise TimeoutError
print('N',N,'constant rank',len(basis),'residualcols',sorted({j for row,l in R for j in row}),'rows',len(R),'seconds',time.time()-st,flush=True)
for row,l in R[:20]:print(l,{j:str(factor(v.as_expr())) for j,v in row.items()},flush=True)
assert len(basis)==Q-1 and all(len(r)==1 for r,l in R)
if all(len(r)==1 for r,l in R):
 gg=None
 for r,l in R:
  p=list(r.values())[0].numer.as_expr();gg=p if gg is None else pgcd(gg,p)
 print('GCD',factor(gg),flush=True)
expected=5*symbols('t')+(18 if N==21 else 19)
assert Poly(gg,symbols('t')).monic()==Poly(expected,symbols('t')).monic()
# For every other lambda5, the leading matrix is invertible at h=1.
# At the sole exceptional lambda5, check invertibility at h=2 modulo
# a prime, which is an exact nonvanishing certificate over Q.
forced=Rational(-18,5) if N==21 else Rational(-19,5)
point2={xx:4,yy:9,zz:(49 if N==21 else 121),aa:point[aa],bb:25}
prime=1000003;numeric=[]
for row,lab in original:
 rr={}
 for j,v in row.items():
  num,den=v.as_expr().subs(point2).as_numer_denom()
  assert int(den)%prime
  value=int(num)*pow(int(den),-1,prime)%prime
  if value:rr[j]=value
 numeric.append(rr)
for j in range(Q//5):
 rr={j+k*(Q//5):Rational(1) for k in range(5)}
 for col,v in [(5*j%Q,-forced/25),(25*j%Q,Rational(1,625))]:rr[col]=rr.get(col,Rational(0))+v
 out={}
 for i,v in rr.items():
  num,den=v.as_numer_denom();out[i]=int(num)*pow(int(den),-1,prime)%prime
 numeric.append({i:v for i,v in out.items() if v})
nb={}
for rr in numeric:
 rr=rr.copy()
 while rr:
  j=min(rr)
  if j not in nb:
   inverse=pow(rr[j],-1,prime);nb[j]={i:v*inverse%prime for i,v in rr.items()};break
  coefficient=rr[j]
  for i,v in nb[j].items():
   value=(rr.get(i,0)-coefficient*v)%prime
   if value:rr[i]=value
   else:rr.pop(i,None)
assert len(nb)==Q
print('EXTRA_PRIME5_CERTIFICATE_VERIFIED',N,'h2 rank',len(nb),'forced lambda5',forced)

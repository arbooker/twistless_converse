"""N=21, Q=42: exact leading-system determinants, including all local signs.

X_p=p**(k/2-s); L=a_2*2**(1-k/2).
The bad-prime normalized coefficients are sigma3,sigma7 in {+1,-1}.
E is the eigenvalue of weight-k W_21 (epsilon_f*i**k).
Only leading Taylor coefficients are used: this is not modularity.
"""
import sympy as S
from sympy.polys.matrices import DomainMatrix
from math import gcd,lcm,isqrt
from itertools import product
import json
from pathlib import Path
X,Y,Z,L=S.symbols('X Y Z L')
Q=42;N=21

def divisors(n):return [i for i in range(1,n+1) if n%i==0]

def mono(r,vals):
 r=S.Rational(r);v=S.Integer(1)
 for p in (2,3,7):
  n=0
  while r.p%p==0:r/=p;n+=1
  while r.q%p==0:r*=p;n-=1
  v*=vals[p]**(-n)
 assert r==1
 return v

def rows(E,sigma3,sigma7,vals=None,lam=L):
 vals=vals or {2:X,3:Y,7:Z};sig={3:sigma3,7:sigma7};out={}
 for q in divisors(Q):
  ell=lcm(N,q*q)
  if Q*Q%ell:continue
  offsets=[a*(Q//q) for a in range(q) if gcd(a,q)==1]
  row=[S.Integer(0)]*Q
  for j in offsets:row[j]+=1
  out[('R',q)]=row
  D=Q*Q//ell
  for t0 in divisors(D):
   for t in (t0,-t0):
    u=-D//t;sign=E
    for p in (3,7):
     if q%p==0:sign*=-sig[p]
    c=sign*mono(S.Rational(ell*t*t,Q*Q),vals)
    row=[S.Integer(0)]*Q
    for a in offsets:row[(a+t)%Q]+=1;row[(a+u)%Q]-=c
    out[('T',q,t)]=row
 for p in (2,3,7):
  for j in range(Q//p):
   row=[S.Integer(0)]*Q
   for a in range(p):row[j+a*(Q//p)]+=1
   row[p*j%Q]-=(lam if p==2 else sig[p])*vals[p]
   if p==2:row[p*p*j%Q]+=vals[p]**2
   out[('H',p,j)]=row
 return out

def select(rr,prime=1000003):
 basis={};labels=[]
 for lab,values in rr.items():
  row={i:int(S.numer(v))%prime*pow(int(S.denom(v)),-1,prime)%prime for i,v in enumerate(values) if v}
  row={i:v for i,v in row.items() if v}
  while row:
   j=min(row)
   if j not in basis:
    v=pow(row[j],-1,prime);basis[j]={i:c*v%prime for i,c in row.items()};labels.append(lab);break
   v=row[j]
   for i,c in basis[j].items():
    w=(row.get(i,0)-v*c)%prime
    if w:row[i]=w
    else:row.pop(i,None)
 return labels

def determinant(signs,labels,point):
 rr=rows(*signs,dict(zip((2,3,7),map(S.Integer,point))))
 mat=S.Matrix([rr[lab] for lab in labels])
 dm=DomainMatrix.from_Matrix(mat)
 return S.factor(dm.domain.to_sympy(dm.det()))

if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser();ap.add_argument('--signs',nargs=3,type=int);args=ap.parse_args()
 answers=[]
 for signs in [tuple(args.signs)] if args.signs else product((-1,1),repeat=3):
  labels=select(rows(*signs,{2:S.Integer(2),3:S.Integer(3),7:S.Integer(5)},S.Integer(11)))
  print('signs',signs,'rank',len(labels),flush=True)
  ans={'signs':signs,'rank':len(labels),'selected_rows':labels}
  if len(labels)==Q:
   rr=rows(*signs)
   dm=DomainMatrix.from_Matrix(S.Matrix([rr[lab] for lab in labels])).to_field()
   det=S.factor(dm.domain.to_sympy(dm.det()))
   E,u,v=signs
   expected=u*X**2/Z*((L*X+1)*Z*(Y-u)+(E*u*v-1)*X**2*Y*Z-E*u*X**2*Y-u*X**2*Z)
   assert S.cancel(det-expected)==0
   ans['symbolic_determinant']=str(det)
   print('symbolic determinant verified',det,flush=True)
   polys=[]
   for point in [(2,3,5),(3,5,7),(5,7,11)]:
    det=determinant(signs,labels,point)
    p=S.Poly(det,L).monic().as_expr() if det else S.Integer(0)
    polys.append(p);g=S.gcd_list(polys)
    print('point',point,'monic determinant',p,'gcd',g,flush=True)
    if g==1:break
   ans['points']=[(2,3,5),(3,5,7),(5,7,11)][:len(polys)]
   ans['monic_determinants']=list(map(str,polys));ans['gcd']=str(g)
  answers.append(ans)
 Path(__file__).with_name('level21_certificate'+('_'+'_'.join(map(str,args.signs)) if args.signs else '')+'.json').write_text(json.dumps(answers,indent=2))

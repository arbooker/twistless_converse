"""Exact division-free first-Taylor pole constraints for the N33 Q66 grid.
Run with ETA BAD3 BAD11. Physical pole interpretation is separate.
"""
from pathlib import Path
exec(Path(__file__).with_name('level33_jet_builder.py').read_text())
original=[(dict(row),lab) for row,lab in R]
R=[(dict(row),i) for i,(row,lab) in enumerate(original)]
def safe(v):
 return len(v.numer.terms())==len(v.denom.terms())==1 and not any(v.numer.terms()[0][0][3:]) and not any(v.denom.terms()[0][0][3:])
def shift(v,n=1):
 def poly(p):return K(K.ring.from_dict({pw:cf/(2**(n*pw[0])*3**(n*pw[1])*11**(n*pw[2])) for pw,cf in p.terms()}))
 return poly(v.numer)/poly(v.denom)
piv=[];operations=[];zeroids=[]
while R:
 choices=[i for i,(r,l) in enumerate(R) if any(safe(v) for v in r.values())]
 if not choices:break
 ii=min(choices,key=lambda i:len(R[i][0]));row,rid=R.pop(ii)
 j=min((j for j,v in row.items() if safe(v)),key=lambda j:sum(j in rr for rr,ll in R))
 val=row[j];row={c:v/val for c,v in row.items()};piv.append((j,row,rid));updates=[];new=[]
 for rr,rid2 in R:
  if j in rr:
   v=rr[j];updates.append((rid2,v))
   for c,u in row.items():
    rr[c]=rr.get(c,K.zero)-v*u
    if not rr[c]:del rr[c]
  if rr:new.append((rr,rid2))
  else:zeroids.append(rid2)
 operations.append((rid,val,updates));R=new
free=[j for j in range(Q) if j not in [j for j,row,rid in piv]]
assert len(free)==2
kernels=[];sources=[]
for col in free:
 pole=[K.zero]*Q;pole[col]=K.one
 for j,row,rid in reversed(piv):pole[j]=-sum((v*pole[c] for c,v in row.items() if c!=j),K.zero)
 kernels.append(pole)
 def rhs(lab):
  if lab[0]=='g':
   _,A,B,C,D,mu,j=lab;den=C*j+D*Q;beta=Q*(A*j+B*Q)//den%Q;det=A*D-B*C
   return shift(mu*mon(Fraction(den*den,det*Q*Q)))*K(Fraction(C*den,det*Q))*pole[beta]
  if lab[0]=='F':
   _,q,t=lab;ell=lcm(N,q*q);u=-(Q*Q//ell)//t
   leading=eta*(-bad3 if q%3==0 else 1)*(-bad11 if q%11==0 else 1)*mon(Fraction(ell*t*t,Q*Q))
   off=[a0*(Q//q) for a0 in range(q) if gcd(a0,q)==1]
   return shift(leading)*K(Fraction(ell*t,Q))*sum((pole[(j+u)%Q] for j in off),K.zero)
  return K.zero
 bvec=[rhs(lab) for row,lab in original]
 for rid,val,updates in operations:
  bvec[rid]/=shift(val)
  for rid2,coef in updates:bvec[rid2]-=shift(coef)*bvec[rid]
 sources.append(bvec)
lead=list(dict.fromkeys(tuple(row.get(j,K.zero) for j in free) for row,rid in R))
jet=list(dict.fromkeys(tuple(col[rid] for col in sources) for rid in zeroids if any(col[rid] for col in sources)))

from sympy import symbols,Poly,groebner,factor,expand
xx,yy,zz,aa,X,A=symbols('x y z a X A')
polys=[];leading_polys=[]
for i,r in enumerate(lead+jet):
 for jt,t in enumerate((lead+jet)[i+1:],i+1):
  det=r[0]*t[1]-r[1]*t[0]
  if not det:continue
  terms={}
  exps=[]
  for (ix,iy,iz,ia,ib),cf in det.numer.terms():
   assert ib==0
   exps.append((ix-ia,iy,iz,ia,cf))
  low=min(e[0] for e in exps)
  parity=low%2
  offset=low
  for ix,iy,iz,ia,cf in exps:
   assert (ix-offset)%2==0
   key=((ix-offset)//2,iy,iz,ia);terms[key]=cf
  pp=Poly.from_dict(terms,(X,yy,zz,A)).as_expr()
  pp=Poly(pp,(A,X,yy,zz)).primitive()[1].monic().as_expr()
  if pp not in polys:polys.append(pp)
  if jt<len(lead) and pp not in leading_polys:leading_polys.append(pp)
polys.sort(key=lambda p:(Poly(p,A,X,yy,zz).total_degree(),len(Poly(p,A,X,yy,zz).terms())))
import json
assert any(expand(p*2-(A+X)*(A+X+1)*(2*yy-3*bad3))==0 for p in polys)
results={}
for name,sub,gens in [('A=-X',{A:-X},(zz,X,yy)),
                      ('A=-X-1',{A:-X-1},(zz,X,yy)),
                      ('y=3bad3/2',{yy:QQ(3,2)*bad3},(zz,A,X))]:
 ps=list(dict.fromkeys(expand(p.subs(sub)) for p in polys))
 ps=[p for p in ps if p]
 ps.sort(key=lambda p:(Poly(p,*gens).total_degree(),len(Poly(p,*gens).terms())))
 G=groebner(ps,*gens,method='f5b')
 Y=-bad3*yy
 P=704*Y**7+8128*Y**6+3072*Y**5+19152*Y**4-14256*Y**3+35640*Y**2-36693*Y+16767
 XP=-(3930080*Y**7+65606464*Y**6+276492600*Y**5+505558764*Y**4+735197796*Y**3+544159053*Y**2+242265654*Y-124273359)/QQ(702348489)
 ZP=(155011648*Y**7+2284015184*Y**6+6550895160*Y**5+8427041640*Y**4+12021412338*Y**3-9889834806*Y**2+21913762599*Y+5678262648)/QQ(6321136401)
 expected={'A=-X':[X**2-bad3*yy-1],
           'A=-X-1':[zz-eta*bad3*(ZP-1)+bad11,X-XP,(Y+3)*P],
           'y=3bad3/2':[A+X,X**2-QQ(5,2)]}[name]
 assert list(G)==list(groebner(expected,*gens,domain='QQ')),(name,G,expected)
 results[name]=[str(p) for p in G]
 print(name,[factor(p) for p in G],flush=True)
Path('/tmp/level33_firstjet_'+''.join('p' if v==1 else 'm' for v in (eta,bad3,bad11))+'.json').write_text(json.dumps({'signs':[eta,bad3,bad11],'free':free,'leading_rank':len(piv),'minors':len(polys),'branches':results},indent=2))
print('N33_FIRST_JET_BRANCHES_VERIFIED',eta,bad3,bad11,flush=True)

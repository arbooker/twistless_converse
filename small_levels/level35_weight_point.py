"""Exact selected leading-row certificate for all weight-point cases.
The accompanying TeX supplies elementary inequalities in integer m>=1.
"""
from pathlib import Path
import json,hashlib
import sympy as s
D=json.loads(Path(__file__).with_name('level35_weight_rows.json').read_text())
assert D['projection_sha256']==hashlib.sha256(Path(__file__).with_name('level35_leading_projection.py').read_bytes()).hexdigest()
x,y,z,w,a,b,r=s.symbols('x y z w a b r');X=x*x;Y=y*y
for name in ['generic','positive']:
 d=D[name];fresh=Path('/tmp/level35_leading_'+name+'.json')
 if fresh.exists():
  f=json.loads(fresh.read_text())
  for i,row in d['rows'].items():assert row==f['rows'][int(i)]
 rows={int(i):{int(j):s.sympify(v) for j,v in row.items()} for i,row in d['rows'].items()}
 def c(i,j):return rows[i].get(j,s.S.Zero)
 def eq(p,q):assert s.cancel(p-q)==0
 assert d['free']==[24,42,126,128,140,158] and d['target']=={'140':'-2'}
 assert set(rows[46])=={42} and set(rows[125])=={140}
 eq(c(46,42),-2*(X+a*x+1)/X);eq(c(125,140),(X+a*x+1)/X)
 assert set(rows[41])=={42,126,140}
 eq(c(41,126),(X*X-2*X+a*x-Y)/Y)
 assert set(rows[3])<={24,42,126,140}
 H=2*x**3*a+X*a*a+X-3;eq(c(3,24),H)
 det=c(67,128)*c(148,158)-c(67,158)*c(148,128)
 eq(det,(x-a)*(a*a*X+a*x**3+a*x+X*X-X+1)/x**3)
 shifted={a:-x/r-r/x}
 eq(H.subs(shifted),-(2*r-1)*X*X/r**2+(3-2*r)*X+r*r-3)
 eq((a*a*X+a*x**3+a*x+X*X-X+1).subs(shifted),(r*r-r+1)*(X*X/r**2-X/r+1))
 sub={a:-x-1/x};P1=b*y+X+Y+1;P2=X*X-X-b*y-2;A=X*X+Y-1;C=X*X-3*X-Y-1
 eq(c(150,42).subs(sub),-2*P1/Y)
 eq(c(159,126).subs(sub),-P2/Y)
 eq(c(159,42).subs(sub),(-A+2*P1)/Y)
 eq(c(41,126).subs(sub),C/Y)
 eq((c(41,42)-c(41,126)).subs(sub),P1/Y)
 eq(c(41,140),(z-1)/z)
 sub2={a:-x-1/x,b:(X*X-X-2)/y}
 det2=c(41,126)*c(220,140)-c(41,140)*c(220,126)
 expected=C*(X*z-X-w-1)/(w*Y) if name=='generic' else -C*(X*z-X+w+1)/(w*Y)
 eq(det2.subs(sub2),expected)
 sub1={a:-x-1/x,b:-(X+Y+1)/y}
 v24=s.cancel((c(3,126)-c(3,42)).subs(sub1)/H.subs(sub1))
 residual=s.cancel(c(0,24).subs(sub1)*v24+(c(0,42)-c(0,126)).subs(sub1))
 num=s.fraction(residual)[0]
 expected=-(X*X+1)*(X*X-2*X-1)*(z-w-1) if name=='generic' else (X*X+1)*(X*X-2*X-1)*(z+w-3)
 assert s.cancel(num/expected).is_Rational
 assert s.cancel(num/expected)!=0
 print(name,'ALL LEADING IDENTITIES PASS',flush=True)
assert 16-5*4//2-2-9==-5
assert 16**2>s.Rational(5,2)*4**2+2+9**2
assert 16-3*4-9-1==-6
assert 16**2>3*4**2+9**2+1
assert all(e*5+f*7!=3 for e in [-1,1] for f in [-1,1])
print('WEIGHT POINT CERTIFICATE PASS')

"""Exact rational isolation of the seven algebraic N33 first-jet candidates.

Every root Y either has |Y|<1 or has |X(Y)|<|Y|. Thus no candidate
can satisfy |X|=4^t, |Y|=3^t for t>=0. No floating-point tests are used.
"""
import json
from pathlib import Path
import sympy as s
Y=s.symbols('Y')
P=704*Y**7+8128*Y**6+3072*Y**5+19152*Y**4-14256*Y**3+35640*Y**2-36693*Y+16767
XP=-(3930080*Y**7+65606464*Y**6+276492600*Y**5+505558764*Y**4+735197796*Y**3+544159053*Y**2+242265654*Y-124273359)/s.Integer(702348489)
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def neg(a):return (-a[1],-a[0])
def mul(a,b):
 vals=[x*y for x in a for y in b]
 return (min(vals),max(vals))
def cmul(a,b):return (add(mul(a[0],b[0]),neg(mul(a[1],b[1]))),add(mul(a[0],b[1]),mul(a[1],b[0])))
def value(poly,box):
 out=((s.S.Zero,s.S.Zero),(s.S.Zero,s.S.Zero))
 for c in s.Poly(poly,Y).all_coeffs():
  out=cmul(out,box);out=(add(out[0],(c,c)),out[1])
 return out
def square(a):
 low=0 if a[0]<=0<=a[1] else min(a[0]**2,a[1]**2)
 return low,max(a[0]**2,a[1]**2)
def norm2(a):return add(square(a[0]),square(a[1]))
real,nonreal=s.Poly(P,Y).intervals(all=True,eps=s.Rational(1,10**14))
assert sum(m for box,m in real+nonreal)==7
assert s.gcd(P,s.diff(P,Y))==1
boxes=[((lo,hi),(s.S.Zero,s.S.Zero)) for (lo,hi),m in real]
for (lo,hi),m in nonreal:
 lr,li=lo.as_real_imag();hr,hi=hi.as_real_imag()
 boxes.append(((lr,hr),(li,hi)))
records=[]
for box in boxes:
 yn=norm2(box);xn=norm2(value(XP,box))
 reason='abs_Y_below_1' if yn[1]<1 else 'abs_X_below_abs_Y'
 assert yn[1]<1 or xn[1]<yn[0],(box,yn,xn)
 records.append({'box':[[str(v) for v in interval] for interval in box],
                 'Y_norm2':[str(v) for v in yn],'X_norm2':[str(v) for v in xn],
                 'exclusion':reason})
Path('/tmp/level33_septic_roots.json').write_text(json.dumps(records,indent=2))
print('N33_SEPTIC_ROOTS_EXCLUDED_EXACTLY',len(records),[r['exclusion'] for r in records])

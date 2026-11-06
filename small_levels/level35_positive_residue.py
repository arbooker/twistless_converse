"""Emit the exact positive-product N35 unshifted residue certificate.
Requires /tmp/level35_firstjet_positive.json from the same first-jet
projection with sign arguments 1 -1 -1 and its output path changed.
No coordinate outside the four-coordinate subsystem is discarded.
"""
from pathlib import Path
import json,hashlib
from sympy.polys.fields import field
from sympy import QQ
root=Path(__file__).resolve().parent
D=json.loads((root/'level35_positive_rows.json').read_text());fresh=json.loads(Path('/tmp/level35_firstjet_positive.json').read_text())
for n,h in D['sources'].items():assert hashlib.sha256((root/n).read_bytes()).hexdigest()==h
assert D['target']==fresh['target']
for i,r in D['rows'].items():
 assert r==fresh['rows'][int(i)]
 assert '128' not in r and '158' not in r
K,b=field('b',QQ);ctx=dict(x=K.one,y=K.one,z=K.one,w=-K.one,a=-2*K.one,b=b)
for j in D['columns']:
 def cv(i):return K(eval(D['rows'][str(i)].get(str(j),'0'),{'__builtins__':{}},ctx))
 assert 2*(cv(3)+cv(14)+cv(19)-cv(45))+3*cv(150)==(-8 if j==192 else 0)
neg=json.loads((root/'level35_unshifted_rows.json').read_text())
assert D['rows']['150']==neg['rows']['150']
assert D['rows']['159']==neg['rows']['159']
assert D['rows']['0']['24']==neg['rows']['0']['24']
assert D['rows']['163']['24']==neg['rows']['163']['24']
print('POSITIVE CENTRAL AND SIMPLE-ZERO ROW IDENTITIES PASS')
ids=sorted(map(int,D['rows']));ix={i:j+1 for j,i in enumerate(ids)};f=lambda v:v.replace('**','^')
s=['K<x,y,z>:=FunctionField(Rationals(),3);w:=-x^2*z+x^2-1;a:=-x-1/x;b:=(x^4-x^2-2)/y;rows:=[];']
for i in ids:s.append('Append(~rows,[K|'+','.join(f(D['rows'][str(i)].get(str(j),'0')) for j in [24,42,84,192])+']);')
s += [f'uu:=[x^2*rows[{ix[0]}][j]+y^2*rows[{ix[163]}][j]:j in [1..4]];assert uu[1] eq -4;',
'v84:=-w*(z-1)/(x^4-3*x^2-y^2-1);v24:=(uu[3]*v84+uu[4])/4;',
'R<Z,Y,X>:=PolynomialRing(Rationals(),3,"grevlex");',
'''function ep(p)
 out:=R!0;ms:=Monomials(p);cs:=Coefficients(p);
 for i in [1..#ms] do es:=Exponents(ms[i]);assert es[1] mod 2 eq 0 and es[2] mod 2 eq 0;
 out+:=cs[i]*X^(es[1] div 2)*Y^(es[2] div 2)*Z^es[3];end for;return out;end function;''','ps:=[];']
for i in [3,13,14,16,18]:s.append(f'r:=rows[{ix[i]}];Append(~ps,ep(Numerator(r[1]*v24+r[3]*v84+r[4])));')
rd=json.loads((root/'level35_positive_root_disks.json').read_text());p=f(rd['p'].replace('XX','X'));yp=f(rd['Y_of_X'].replace('XX','X'));zp=f(rd['Z_of_X'].replace('XX','X'))
s+=['I:=ideal<R|ps>;J:=Saturation(I,ideal<R|(Z-1)*(X^2+Y-1)*(X^2-3*X-Y-1)*X*Y*Z*(-X*Z+X-1)>);',
'assert (X+1)*('+p+') in J;assert (X+1)*(Y-('+yp+')) in J;assert (X+1)*(Z-('+zp+')) in J;assert Z-3 in J+ideal<R|X+1>;',
'print "POSITIVE GENERIC BRANCH CERTIFICATE PASS";',
'L<U,V>:=FunctionField(Rationals(),2);P<t>:=PolynomialRing(L);',
'''function red(f)
 n:=Evaluate(Numerator(f),[P!U,t,P!V]) mod (t^2+U^4-1);
 d:=Evaluate(Denominator(f),[P!U,t,P!V]) mod (t^2+U^4-1);
 assert Degree(n) le 0 and Degree(d) eq 0;return Coefficient(n,0)/Coefficient(d,0);end function;''',
'rr:=[[red(v):v in r]:r in rows];uu:=[red(v):v in uu];c:=red(-w*(z-1)/(2*x^4-3*x^2-2));v0:=(uu[3]*c+uu[4])/4;v1:=(uu[2]-uu[3])/4;',
'S<T,Z,X>:=PolynomialRing(Rationals(),3,"grevlex");',
'''function hp(p)
 out:=S!0;ms:=Monomials(p);cs:=Coefficients(p);
 for i in [1..#ms] do es:=Exponents(ms[i]);assert es[1] mod 2 eq 0;
 out+:=cs[i]*X^(es[1] div 2)*Z^es[2];end for;return out;end function;''','ps:=[];']
for i in [3,16,164,13]:s.append(f'r:=rr[{ix[i]}];p:=r[1]*v1+r[2]-r[3];q:=r[1]*v0+r[3]*c+r[4];dd:=LCM(Denominator(p),Denominator(q));assert Denominator(p*dd) eq 1 and Denominator(q*dd) eq 1;Append(~ps,hp(Numerator(p*dd))*T+hp(Numerator(q*dd)));')
s+=['I:=ideal<S|ps>;J:=Saturation(I,ideal<S|X*Z*(-X*Z+X-1)*(2*X+1)*(X-2)*(1-X^2)*(Z-1)>);assert 1 in J;print "POSITIVE A=0 BRANCH CERTIFICATE PASS";quit;']
path=Path('/tmp/level35_positive_residue.m');path.write_text('\n'.join(s)+'\n');print(path)

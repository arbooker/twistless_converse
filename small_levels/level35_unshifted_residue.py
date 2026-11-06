"""Emit a bounded Magma verifier for selected level-35 first-jet identities.

This certifies the stated leading-residue algebra, not complete pole cancellation.
First regenerate /tmp/level35_firstjet_reduced.json with
level35_firstjet_projection.py; this emitter verifies every selected row
against that fresh output and checks the generator source hashes.
Then run magma -b /tmp/level35_unshifted_residue.m.
"""
from pathlib import Path
import json,hashlib
root=Path(__file__).resolve().parent
D=json.loads((root/'level35_unshifted_rows.json').read_text())
for name,digest in D['sources'].items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest
fresh=json.loads(Path('/tmp/level35_firstjet_reduced.json').read_text())
assert D['target']==fresh['target']
for i,r in D['rows'].items():
 assert r==fresh['rows'][int(i)]
 assert '128' not in r and '158' not in r
from sympy.polys.fields import field
from sympy import QQ
KC,bc=field('b',QQ)
central_context=dict(x=KC.one,y=KC.one,z=KC.one,w=-KC.one,a=-2*KC.one,b=bc)
for j in D['columns']:
 def cv(i):return KC(eval(D['rows'][str(i)].get(str(j),'0'),{'__builtins__':{}},central_context))
 assert 2*(cv(104)-cv(19)+cv(45))+5*cv(150)==(-8 if j==192 else 0)
print('CENTRAL SIGNED BRANCH CERTIFICATE PASS')
# Exact coefficient identity controlling the fourth coordinate's pole order.
KO,xo,yo,zo,wo,bo=field('x,y,z,w,b',QQ)
ctx=dict(x=xo,y=yo,z=zo,w=wo,a=-xo-1/xo,b=bo)
c0=KO(eval(D['rows']['0']['24'],{'__builtins__':{}},ctx))
c163=KO(eval(D['rows']['163']['24'],{'__builtins__':{}},ctx))
assert xo**2*c0+yo**2*c163==-4
print('LAURENT ORDER COEFFICIENT IDENTITY PASS')
indices=sorted(map(int,D['rows']));m={i:j+1 for j,i in enumerate(indices)}
f=lambda v:v.replace('**','^')
s=['K<x,y,z>:=FunctionField(Rationals(),3);',
   'w:=x^2*z-x^2-1; a:=-x-1/x; b:=(x^4-x^2-2)/y;', 'rows:=[];']
for i in indices:
 r=D['rows'][str(i)]
 s.append('Append(~rows,[K|'+','.join(f(r.get(str(j),'0')) for j in [24,42,84,192])+']);')
s += ['R<Z,Y,X>:=PolynomialRing(Rationals(),3,"grevlex");',
'''function evenpoly(p)
 out:=R!0; ms:=Monomials(p); cs:=Coefficients(p);
 for i in [1..#ms] do e:=Exponents(ms[i]); assert e[1] mod 2 eq 0 and e[2] mod 2 eq 0;
 out+:=cs[i]*X^(e[1] div 2)*Y^(e[2] div 2)*Z^e[3]; end for;
 return out;
end function;''',
 'v84:=K!1; v192:=(x^4-3*x^2-y^2-1)/(w*(z-1));',
 f'r:=rows[{m[104]}]; v24:=-(r[3]+r[4]*v192)/r[1];',
 'ps:=[];']
for i in [16,3,164]:s.append(f'r:=rows[{m[i]}]; Append(~ps,evenpoly(Numerator(r[1]*v24+r[3]+r[4]*v192)));')
rd=json.loads((root/'level35_unshifted_root_disks.json').read_text())
p17=rd['p'].replace('XX','X').replace('**','^')
y_of_x=rd['Y_of_X'].replace('XX','X').replace('**','^')
s+=['I:=ideal<R|ps>; prod:=(Z-1)*(X^2+Y-1)*(X^2-X+Y+3)*(X^2-3*X-Y-1);',
    'J:=Saturation(I,ideal<R|prod*(X^3+1)>);',
    'assert ('+p17+') in J; assert Y-('+y_of_x+') in J;',
    'J0:=Saturation(I+ideal<R|X^3+1>,ideal<R|prod>); assert 1 in J0;',
    'print "GENERIC BRANCH CERTIFICATE PASS";',
 'L<U,V>:=FunctionField(Rationals(),2); P<t>:=PolynomialRing(L);',
'''function red(f,rel)
 n:=Evaluate(Numerator(f),[P!U,t,P!V]) mod rel;
 d:=Evaluate(Denominator(f),[P!U,t,P!V]) mod rel;
 assert Degree(n) le 0 and Degree(d) eq 0;
 return Coefficient(n,0)/Coefficient(d,0);
end function;
S<v,u>:=PolynomialRing(Rationals(),2,"grevlex");
function halfpoly(p)
 out:=S!0; ms:=Monomials(p); cs:=Coefficients(p);
 for i in [1..#ms] do e:=Exponents(ms[i]); assert e[1] mod 2 eq 0;
 out+:=cs[i]*u^(e[1] div 2)*v^e[2]; end for; return out;
end function;''',
 'rel:=t^2+U^4-U^2+3; rr:=[[red(q,rel):q in r]:r in rows];',
 'v84:=red(w*(z-1)/(x^4-3*x^2-y^2-1),rel);',
 f'r:=rr[{m[0]}]; assert r[1] eq (U^4+2)*(U^4-U^2+2)/U^2; v24:=-(r[3]*v84+r[4])/r[1]; ps:=[];']
for i in [13,14,19,21,163]:s.append(f'r:=rr[{m[i]}]; Append(~ps,halfpoly(Numerator(r[1]*v24+r[3]*v84+r[4])));')
s += ['I:=ideal<S|ps>; assert (v-1)*(u^2+2) in I; print "D=0 BRANCH CERTIFICATE PASS";',
 'rel:=t^2+U^4-1; rr:=[[red(q,rel):q in r]:r in rows];',
 'c:=red(w*(z-1)/(2*x^4-3*x^2-2),rel);',
 f'r:=rr[{m[104]}]; assert r[1] eq U^2-4; v0:=-(r[3]*c+r[4])/r[1]; v1:=-(r[2]-r[3])/r[1];',
 f'r:=rr[{m[0]}]; pv:=r[1]*v1+r[2]-r[3]; qv:=r[1]*v0+r[3]*c+r[4];',
 'assert pv eq -U^2*(U^4+1)*(U^2*V-U^2-V)/(U^2*V-U^2-1); VV:=-qv/pv; ps:=[];']
for i in [9,26,16,163]:s.append(f'r:=rr[{m[i]}]; Append(~ps,halfpoly(Numerator(r[1]*(v0+v1*VV)+(r[2]-r[3])*VV+r[3]*c+r[4])));')
s += ['I:=ideal<S|ps>; assert (v-1)*(u-4) in I; print "A=0 BRANCH CERTIFICATE PASS";', 'quit;']
path=Path('/tmp/level35_unshifted_residue.m');path.write_text('\n'.join(s)+'\n');print(path)

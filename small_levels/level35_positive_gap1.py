"""Emit a bounded exact Magma certificate for the positive-product n=1 branch."""
from pathlib import Path
import json,hashlib
D=json.loads(Path(__file__).with_name('level35_positive_gap1_rows.json').read_text())
assert D['projection_source_sha256']==hashlib.sha256(Path(__file__).with_name('level35_firstjet_projection.py').read_bytes()).hexdigest()
fresh=Path('/tmp/level35_firstjet_positive.json')
if fresh.exists():
 F=json.loads(fresh.read_text())
 for i,r in D['rows'].items():assert r==F['rows'][int(i)]
cols=['24','84','128','158'];ids=list(D['rows']);out=['K<x,y,z,w>:=FunctionField(Rationals(),4);a:=-x/2-2/x;b:=(x^4-x^2/2-3)/y;rows:=[];']
for i in ids:
 r=D['rows'][i];out.append('Append(~rows,[K|'+','.join(r.get(j,'0').replace('**','^') for j in cols)+']);')
out+=['L<U,Z,W>:=FunctionField(Rationals(),3);P<t>:=PolynomialRing(L);',
'function red(f) rel:=t^2-U^4+5/2*U^2+2;n:=Evaluate(Numerator(f),[P!U,t,P!Z,P!W]) mod rel;d:=Evaluate(Denominator(f),[P!U,t,P!Z,P!W]) mod rel;assert Degree(n) le 0 and Degree(d) eq 0;return Coefficient(n,0)/Coefficient(d,0);end function;',
'rows:=[[red(v):v in r]:r in rows];']
idx=lambda i:ids.index(str(i))+1
out += [f'r:=rows[{idx(3)}];v24:=-r[2]/r[1];r:=rows[{idx(67)}];t:=rows[{idx(148)}];det:=r[3]*t[4]-r[4]*t[3];br:=-r[1]*v24-r[2];bt:=-t[1]*v24-t[2];v128:=(br*t[4]-bt*r[4])/det;v158:=(r[3]*bt-t[3]*br)/det;']
for i,p in D['expected']['rows'].items():
 expr=p.replace('**','^').replace('u','(U^2)');out.append(f'r:=rows[{idx(int(i))}];v:=r[1]*v24+r[2]+r[3]*v128+r[4]*v158;assert L!Numerator(v) eq ({expr});')
out+=['R<u,Z,W>:=PolynomialRing(Rationals(),3); ds:=[];']
for cert in D['expected']['determinants']:
 vals=[]
 for i in cert['indices']:
  p=D['expected']['rows'][str(i)].replace('**','^')
  vals.append(p)
 out.append('ps:=['+','.join(vals)+'];')
 out.append('M:=Matrix(R,3,3,[Derivative(p,2):p in ps] cat [Derivative(p,3):p in ps] cat [Evaluate(p,[u,0,0]):p in ps]);')
 # M is transposed coefficient matrix; same determinant.
 out.append('d:=Determinant(M);assert d eq '+cert['det'].replace('**','^')+';Append(~ds,d);')
out+=['assert GCD(ds[1],ds[2]) eq '+D['expected']['gcd'].replace('**','^')+';','print "POSITIVE SHIFT ONE EXACT CERTIFICATE PASS";quit;']
Path('/tmp/level35_positive_gap1_certificate.m').write_text('\n'.join(out))
print('Saved /tmp/level35_positive_gap1_certificate.m')

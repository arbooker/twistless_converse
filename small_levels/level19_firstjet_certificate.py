"""Export the exact N=19 generic first-jet pole certificate; never invokes Magma.

Run from the project root. Output: /tmp/level19_firstjet_certificate.m.
The exported rational Groebner calculation was completed on 2026-10-14;
its saved output is level19_firstjet_gb_Q.txt. This is only the sign
stratum eta=delta=-1 with the exclusions stated in level19_pole_probe.tex.
"""
from pathlib import Path
import sys
sys.argv=[sys.argv[0],'-1','-1']
source=Path(__file__).with_name('level19_pole_probe.py').read_text()
base=source[source.index('import sys,time'):source.index('pivs,jrows=elim(jet,Q)')]
base=base.replace('piv.append(j)','piv.append((j,dict(rr)))')
exec(base)
opivs,orows=elim([(dict(r),l) for r,l in original],Q)
jpivs,jrows=elim(jet,Q)
for rr,ll in jrows:
 for j,pr in opivs:
  val=rr.get(Q+j,K.zero)
  if val:
   for cc,vv in pr.items():
    cc+=Q;rr[cc]=rr.get(cc,K.zero)-val*vv
    if not rr[cc]:del rr[cc]
jrows=[(r,l) for r,l in jrows if r]
left=[(r,l) for r,l in jrows if any(j<Q for j in r)]
cols=[18,42,72,132,156,186]
assert len(left)==60 and len(orows)==27
out=lambda v:str(v).replace('**','^')
head='R<x,y,z,a,b>:=PolynomialRing(Rationals(),5); K:=FieldOfFractions(R);\n'
head+='A:=Matrix(K,60,6,['+','.join(out(r.get(j,K.zero)) for r,l in left for j in cols)+']);\n'
head+='B:=Matrix(K,27,3,['+','.join(out(r.get(j,K.zero)) for r,l in orows for j in [18,42,72])+']);\n'
# Regenerate the independent proportional-row constraints.
exec(source[source.index('import sys,time'):source.index('import sympy as sp')])
J=x**4+(a*a-2)*x*x+1
coefw=-J/(x*a*(y*y+1));seen=set();safe=[]
for rr,ll in result:
 v=rr.get(18,K.zero)*coefw+rr.get(42,K.zero)-rr.get(72,K.zero)
 if v:
  p=v.numer.monic();st=str(p)
  if st not in seen:seen.add(st);safe.append(p)
assert len(safe)==15
head+='Safe:=['+','.join(str(p).replace('**','^') for p in safe)+'];\n'
body=r'''
Al:=Submatrix(A,1,1,60,3); Ar:=Submatrix(A,1,4,60,3);
L:=Matrix(Basis(Kernel(Al)));
Lp:=ZeroMatrix(R,Nrows(L),Ncols(L));
for i in [1..Nrows(L)] do
 d:=LCM([Denominator(c):c in Eltseq(L[i])]);
 for j in [1..Ncols(L)] do Lp[i,j]:=R!(d*L[i,j]); end for;
end for;
assert ChangeRing(Lp,K)*Al eq 0;
C:=ChangeRing(Lp,K)*Ar;
v:=Transpose(Matrix(Vector(K,[-(x^4+(a^2-2)*x^2+1),x*a*(y^2+1),-x*a*(y^2+1)])));
cs:=Eltseq(C*v); bs:=Eltseq(B*v);
G:=x^2-2*x*a+4;
P:=Safe cat [ExactQuotient(Numerator(c),G):c in cs|c ne 0]
        cat [Numerator(c):c in bs|c ne 0];
S<X,Y,Z,AA,BB,TT>:=PolynomialRing(Rationals(),6,"grevlex");
P:=[Evaluate(p,[X,Y,Z,AA,BB]):p in P];
Append(~P,TT*X*Y*Z*AA*(Y^2+1)*(X^4-1)-1);
time GB:=GroebnerBasis(ideal<S|P>);
expected:=[AA^2-9/4,TT^2-1/526702500,X+4/3*AA,Y+68850*TT,Z-17,BB-38250*TT];
assert GB eq expected;
print "Verified exact generic N=19 first-jet certificate",GB;
quit;
'''
Path('/tmp/level19_firstjet_certificate.m').write_text(head+body)
print('Exported /tmp/level19_firstjet_certificate.m; no external algebra process launched.')

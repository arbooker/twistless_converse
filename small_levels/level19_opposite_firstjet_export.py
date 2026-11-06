"""Export the exact N=19 generic first-jet pole certificate; never invokes Magma.

Run from the project root. Output: /tmp/level19_opposite_firstjet_certificate.m.
The exported rational Groebner calculation is NOT yet run. This is the
sign stratum eta=-1, delta=1. All kernel-row denominators are cleared
before obtaining scalar constraints; no common factor is divided out.
"""
from pathlib import Path
import sys
sys.argv=[sys.argv[0],'-1','1']
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
cols=[30,42,76,132,156,186]
assert len(left)==56 and len(orows)==27
out=lambda v:str(v).replace('**','^')
head='R<x,y,z,a,b>:=PolynomialRing(Rationals(),5); K:=FieldOfFractions(R);\n'
head+='A:=Matrix(K,56,6,['+','.join(out(r.get(j,K.zero)) for r,l in left for j in cols)+']);\n'
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
print("Safe constraints",len(safe))
head+='Safe:=['+','.join(str(p).replace('**','^') for p in safe)+'];\n'
body=r'''
Al:=Submatrix(A,1,1,56,3); Ar:=Submatrix(A,1,4,56,3);
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
print "Scalar numerator gcd",GCD([Numerator(c):c in cs|c ne 0]);
P:=Safe cat [Numerator(c):c in cs|c ne 0]
        cat [Numerator(c):c in bs|c ne 0];
S<X,Y,Z,AA,BB,TT>:=PolynomialRing(Rationals(),6,"grevlex");
P:=[Evaluate(p,[X,Y,Z,AA,BB]):p in P];
Append(~P,TT*X*Y*Z*AA*(Y^2+1)*(X^4-1)-1);
time GB:=GroebnerBasis(ideal<S|P>);
print "Opposite-sign exact basis",GB;
PrintFile("/tmp/level19_opposite_firstjet_gb_Q.txt",Sprint(GB));
quit;
'''
Path('/tmp/level19_opposite_firstjet_certificate.m').write_text(head+body)
print('Exported /tmp/level19_opposite_firstjet_certificate.m; no external algebra process launched.')

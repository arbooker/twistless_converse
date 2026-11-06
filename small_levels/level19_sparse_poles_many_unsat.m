SetNthreads(1);SetMemoryLimit(500000000);Alarm(45);SetQuitOnError(true);
SetOutputFile("/tmp/level19_sparse_poles_many_unsat_final.log":Overwrite:=true);
SetGBGlobalModular(false);assert not GetGBGlobalModular();
load "/tmp/level19_sparse_poles_compactall_fast.m";Old:=PP[1..15];
load "/tmp/level19_exact_membership_sparse_fast.m";
Old:=[Polynomial(Coefficients(p),[Monomial(S,Exponents(m)):m in Monomials(p)]):p in Old];
I:=ideal<S|Old cat [PP[i]:i in [8,11,12,13,14,15]]>;
safe:=X*Y*Z*A*(Y+1)*(X^2-1)*(X-2*A+4)*(A^2+(X-1)^2)*(A+(X-1)*Y);
PrintFile("/tmp/level19_sparse_poles_many_unsat_final.stage","UNSAT START":Overwrite:=true);
time GG:=GroebnerBasis(I:GlobalModular:=false,Homogenize:=false);
PrintFile("/tmp/level19_sparse_poles_many_unsat_final.stage","UNSAT DONE " cat Sprint(<#GG,&+[#Monomials(g):g in GG]>));
print GG;PrintFile("/tmp/level19_sparse_poles_many_unsat_basis.m","S<B,A,Z,Y,X>:=PolynomialRing(Rationals(),5,\"grevlex\");GG:=" cat Sprint(GG) cat ";":Overwrite:=true);
for step in [1..3] do
 HH:=[];changed:=false;
 for p0 in GG do
  p:=p0;
  repeat g:=GCD(p,safe);if TotalDegree(g) gt 0 then changed:=true;p:=ExactQuotient(p,g);end if;until TotalDegree(g) eq 0;
  Append(~HH,p);
 end for;
 if not changed then break;end if;
 I:=ideal<S|HH>;GG:=GroebnerBasis(I:GlobalModular:=false,Homogenize:=false);
 PrintFile("/tmp/level19_sparse_poles_many_unsat_final.stage",Sprint(<step,#GG,&+[#Monomials(g):g in GG]>));
end for;
PrintFile("/tmp/level19_sparse_poles_many_unsat_final.stage","STRIP DONE");
for f in [X,Y,A,Z,Y+1,X^2-1,X-2*A+4,A^2+(X-1)^2,A+(X-1)*Y] do
 I:=Saturation(I,ideal<S|f>);GG:=GroebnerBasis(I:GlobalModular:=false,Homogenize:=false);
 PrintFile("/tmp/level19_sparse_poles_many_unsat_final.stage",Sprint(<f,#GG>));
end for;
assert X-4 in I;assert A+3 in I;print GG;
PrintFile("/tmp/level19_sparse_poles_many_unsat_final.pass","PASS":Overwrite:=true);quit;

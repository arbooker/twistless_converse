// Polynomial primitive left-syzygies: safe at every parameter specialization.
SetGBGlobalModular(false);
assert not GetGBGlobalModular();
L:=Matrix(Rationals(),0,4,[]); inds:=[];
for i in [1..#rows] do
 r:=[Evaluate(rows[i][j],[2,3,5,7,11,13]):j in [3..6]];
 LL:=VerticalJoin(L,Matrix(Rationals(),1,4,r));
 if Rank(LL) gt #inds then L:=LL;Append(~inds,i);end if;
 if #inds eq 4 then break;end if;
end for;
assert #inds eq 4;
D:=Matrix(P,4,4,&cat[[rows[i][j]:j in [3..6]]:i in inds]);
E:=Matrix(P,4,2,&cat[[rows[i][j]:j in [1..2]]:i in inds]);
dd:=Determinant(D);assert dd ne 0;
Adj:=Matrix(P,4,4,&cat[[(-1)^(i+j)*Determinant(Matrix(P,3,3,&cat[[D[r,c]:c in [1..4]|c ne i]:r in [1..4]|r ne j])):j in [1..4]]:i in [1..4]]);
assert D*Adj eq dd*IdentityMatrix(P,4);
print "PIVOT_ROWS",inds;
function DividePoly(p,q)
 v,r:=Quotrem(p,q);assert r eq 0;return v;
end function;
EE:=Adj*E; cons:=[* *]; ngcd:=0;
for row in rows do
 if &and[row[j] eq 0:j in [3..6]] then
  Append(~cons,[row[1],row[2]]);
 else
  RR:=Matrix(P,1,4,[row[i+2]:i in [1..4]])*Adj;
  gg:=GCD([dd] cat Eltseq(RR));
  if TotalDegree(gg) gt 0 then ngcd+:=1;end if;
  qq:=DividePoly(dd,gg);ss:=[DividePoly(RR[1,i],gg):i in [1..4]];
  assert qq*Matrix(P,1,4,[row[i+2]:i in [1..4]]) eq Matrix(P,1,4,ss)*D;
  Append(~cons,[qq*row[j]-&+[ss[i]*E[i,j]:i in [1..4]]:j in [1..2]]);
 end if;
end for;
print "PRIMITIVE_CONSTRAINTS",#cons,"GCDS",ngcd;
S<u,A,B,Y,W,z,x,t>:=PolynomialRing(Rationals(),8,"grevlex");
phi:=hom<P->S|x,Y,z,W,A,B>;
for chart in [1..2] do
 polys:=[chart eq 1 select phi(r[1])+u*phi(r[2]) else phi(r[2]):r in cons];
 polys:=[p:p in polys|p ne 0];Append(~polys,t*x*Y*z*W-1);
 I:=ideal<S|polys>;print "IDEAL_BEGIN",chart,#polys;time G:=GroebnerBasis(I : GlobalModular:=false);
 print "IDEAL_RESULT",chart,#G;
 if G eq [S!1] then print "UNIT",chart;continue;end if;
 print "DIMENSION",Dimension(I);
 if Dimension(I) ne 0 then continue;end if;
 J:=EliminationIdeal(I,{S.7,S.4});JJ:=ChangeOrder(J,"lex");GG:=GroebnerBasis(JJ : GlobalModular:=false);
 assert &and[Evaluate(g,[S.i:i in [1..8]]) in I:g in GG];
 print "XY_COUNT",#GG;
 PrintFile("/tmp/level26_negative_poles___CODE___chart" cat IntegerToString(chart) cat "_xy.txt",Sprint(GG):Overwrite:=true);
 for g in GG do print "DEGREES",TotalDegree(g),Degree(g,4),Degree(g,7);end for;
end for;
quit;

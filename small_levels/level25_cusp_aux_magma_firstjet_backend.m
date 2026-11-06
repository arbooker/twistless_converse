// A,J are exact sparse leading/source matrices in K; Q,nonzero2 supplied.
function Safe(v)
 if v eq 0 then return false; end if;
 n:=Numerator(v);d:=Denominator(v);
 if #Monomials(n) ne 1 or #Monomials(d) ne 1 then return false; end if;
 en:=Exponents(Monomials(n)[1]);ed:=Exponents(Monomials(d)[1]);
 cut:=nonzero2 select 6 else 5;
 return &and[en[i] eq 0 and ed[i] eq 0:i in [cut..7]];
end function;
function Shift(v)
 return Evaluate(v,[x/2,y/3,z/5,w/7,a,b,c]);
end function;
procedure ReduceSparse(~A,~active,~piv,~ops,~zeros)
 start:=Cputime();
 while #active gt 0 do
  chosen:=0;best:=10000000;
  for i in active do
   if #Keys(A[i]) lt best and exists{j:j in Keys(A[i])|Safe(A[i][j])} then
    chosen:=i;best:=#Keys(A[i]);
   end if;
  end for;
  if chosen eq 0 then break; end if;
  active:=[i:i in active|i ne chosen];row:=A[chosen];
  candidates:=[j:j in Keys(row)|Safe(row[j])];
  counts:=[#[i:i in active|IsDefined(A[i],j)]:j in candidates];
  _,at:=Min(counts);col:=candidates[at];val:=row[col];
  for j in Keys(row) do row[j]/:=val; end for;
  A[chosen]:=row;Append(~piv,<col,row,chosen>);
  updates:=[];remaining:=[];
  for i in active do
   rr:=A[i];
   if IsDefined(rr,col) then
    co:=rr[col];Append(~updates,<i,co>);
    for j in Keys(row) do
     vv:=IsDefined(rr,j) select rr[j] else K!0;
     vv-:=co*row[j];
     if vv eq 0 then if IsDefined(rr,j) then Remove(~rr,j); end if;
     else rr[j]:=vv; end if;
    end for;
    A[i]:=rr;
   end if;
   if #Keys(rr) eq 0 then Append(~zeros,i);else Append(~remaining,i);end if;
  end for;
  active:=remaining;Append(~ops,<chosen,val,updates>);
  if #piv mod 100 eq 0 then print "PIVOT",#piv,Cputime(start); end if;
 end while;
end procedure;
active:=[i:i in [1..#A]|#Keys(A[i]) gt 0];piv:=[];ops:=[];zeros:=[];
ReduceSparse(~A,~active,~piv,~ops,~zeros);
free:=Sort(Setseq({1..Q} diff {p[1]:p in piv}));
print "LEADING",#piv,free,#active,#zeros;
pol:=[* *];sources:=[* *];
for fc in free do
 pole:=[K!0:i in [1..Q]];pole[fc]:=1;
 for p in Reverse(piv) do
  pole[p[1]]:=-&+[K|p[2][j]*pole[j]:j in Keys(p[2])|j ne p[1]];
 end for;
 Append(~pol,pole);
 rhs:=[&+[K|J[i][j]*pole[j]:j in Keys(J[i])]:i in [1..#J]];
 for op in ops do
  rid:=op[1];if rhs[rid] eq 0 then continue;end if;
  rhs[rid]/:=Shift(op[2]);
  for up in op[3] do rhs[up[1]]-:=Shift(up[2])*rhs[rid];end for;
 end for;
 Append(~sources,rhs);print "SOURCE",#sources;
end for;
C:=[* *];
for i in active do
 rr:=AssociativeArray(Integers());
 for j in [1..#free] do if IsDefined(A[i],free[j]) then rr[j]:=A[i][free[j]];end if;end for;
 Append(~C,rr);
end for;
for i in zeros do
 rr:=AssociativeArray(Integers());
 for j in [1..#free] do if sources[j][i] ne 0 then rr[j]:=sources[j][i];end if;end for;
 if #Keys(rr) gt 0 then Append(~C,rr);end if;
end for;
for j in [1..Q by Q div 5] do
 rr:=AssociativeArray(Integers());
 for i in [1..#free] do if pol[i][j] ne 0 then rr[i]:=pol[i][j];end if;end for;
 if #Keys(rr) gt 0 then Append(~C,rr);end if;
end for;
active:=[1..#C];cpiv:=[];cops:=[];czero:=[];
ReduceSparse(~C,~active,~cpiv,~cops,~czero);
cfree:=Sort(Setseq({1..#free} diff {p[1]:p in cpiv}));
print "JET_REDUCTION",#cpiv,cfree,#active;
if #cfree eq 0 then print "UNIFORM_MONOMIAL_POLE_EXCLUSION";quit;end if;
S:=PolynomialRing(Rationals(),7+#cfree,"grevlex");
AssignNames(~S,["x","y","z","w","a","b","c"] cat ["v" cat IntegerToString(i):i in [1..#cfree-1]] cat ["t"]);
for chart in [1..#cfree] do
 P:=[];
 for rid in active do
  rr:=C[rid];den:=LCM([Denominator(v):v in Values(rr)]);
  eq:=S!0;
  for j in [chart..#cfree] do
   if IsDefined(rr,cfree[j]) then
    coeff:=Numerator(rr[cfree[j]]*den);assert Denominator(rr[cfree[j]]*den) eq 1;
    term:=Evaluate(coeff,[S.i:i in [1..7]]);
    eq+:=j eq chart select term else term*S.(7+j-chart);
   end if;
  end for;
  if eq ne 0 then Append(~P,eq);end if;
 end for;
 sat:=S.1*S.2*S.3*S.4*(nonzero2 select S.5 else S!1);
 Append(~P,S.(Rank(S))*sat-1);
 print "IDEAL_BEGIN",chart,#P;time G:=GroebnerBasis(ideal<S|P>);
 print "IDEAL_RESULT",chart,#G;
 if #G lt 8 then G;end if;
end for;
quit;

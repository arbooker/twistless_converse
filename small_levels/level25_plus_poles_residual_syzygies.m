// Inputs are exact reduced tables Lres,Jres,Craw from the shared first jet.
// Output C consists of existing constraints plus primitive lower-germ syzygies.
function Complexity(v)
 return #Monomials(Numerator(v))+#Monomials(Denominator(v));
end function;
order:=Sort([<&+[Complexity(v):v in Eltseq(Lres[q])] + &+[Complexity(v):v in Eltseq(Jres[q])],q>:q in [1..Nrows(Lres)]]);
order:=[p[2]:p in order];
selected:=[];rank0:=0;
seedOrder:=order[seedoffset+1..#order] cat order[1..seedoffset];
for q in seedOrder do
 trial:=Matrix(K,[Eltseq(Lres[i]):i in selected cat [q]]);
 newrank:=Rank(trial);
 if newrank gt rank0 then Append(~selected,q);rank0:=newrank;end if;
 if rank0 eq Ncols(Lres) then break;end if;
end for;
assert rank0 eq Ncols(Lres);
L:=Matrix(K,[Eltseq(Lres[i]):i in selected]);
detL:=Determinant(L);adjL:=detL*L^-1;
assert L*adjL eq detL*IdentityMatrix(K,Ncols(Lres));
print "SIMPLE_GERM_BASE",selected,"DET",Factorization(Numerator(detL));
C:=[* *];
for row in Rows(Craw) do
 rr:=AssociativeArray(Integers());
 for j in [1..Ncols(Craw)] do if row[j] ne 0 then rr[j]:=row[j];end if;end for;
 if #Keys(rr) gt 0 then Append(~C,rr);end if;
end for;
used:=order[1..Min(limit,#order)];
for q in used do
 coeff:=Vector(K,Eltseq(Lres[q]))*adjL;
 raw:=[detL] cat Eltseq(coeff);
 denominator:=LCM([Denominator(v):v in raw]);
 numerators:=[Numerator(v*denominator):v in raw];
 common:=GCD(numerators);
 primitive:=[K!(v div common):v in numerators];
 front:=primitive[1];coeff:=Vector(K,primitive[2..#primitive]);
 assert front*Vector(K,Eltseq(Lres[q])) eq coeff*L;
 rr:=AssociativeArray(Integers());
 for j in [1..Ncols(Jres)] do
  v:=front*Jres[q,j]-&+[coeff[i]*Jres[selected[i],j]:i in [1..#selected]];
  if v ne 0 then rr[j]:=v;end if;
 end for;
 if #Keys(rr) gt 0 then Append(~C,rr);end if;
end for;
print "PRIMITIVE_GERM_ROWS",#used,"CONSTRAINTS",#C;
free:=[1..Ncols(Craw)];

// Additional exact lower-germ syzygies.  No candidate-pole factor is inverted.
// A and sources are already reduced by monomial units; ``active`` contains
// every nonzero lower residual row. Shift evaluates its coefficient at s-1.
lower:=Matrix(K,[[Shift(IsDefined(A[i],j) select A[i][j] else K!0):j in free]:i in active]);
selected:=[];rank0:=0;
for q in [1..#active] do
 trial:=Matrix(K,[Eltseq(lower[i]):i in selected cat [q]]);
 newrank:=Rank(trial);
 if newrank gt rank0 then Append(~selected,q);rank0:=newrank;end if;
 if rank0 eq #free then break;end if;
end for;
assert rank0 eq #free;
L:=Matrix(K,[Eltseq(lower[i]):i in selected]);
detL:=Determinant(L);adjL:=detL*L^-1;
assert L*adjL eq detL*IdentityMatrix(K,#free);
print "GERM_BASE",selected,"DETERMINANT",Factorization(Numerator(detL));
for q in [1..#active] do
 coeff:=Vector(K,Eltseq(lower[q]))*adjL;
 // Make the complete syzygy primitive, not merely its source constraint.
 // Thus the resulting coefficients are polynomials at every candidate pole.
 raw:=[detL] cat Eltseq(coeff);
 denominator:=LCM([Denominator(v):v in raw]);
 numerators:=[Numerator(v*denominator):v in raw];
 common:=GCD(numerators);
 primitive:=[K!(v div common):v in numerators];
 front:=primitive[1];coeff:=Vector(K,primitive[2..#primitive]);
 rr:=AssociativeArray(Integers());
 for j in [1..#free] do
  v:=front*sources[j][active[q]]-&+[coeff[i]*sources[j][active[selected[i]]]:i in [1..#free]];
  if v ne 0 then rr[j]:=v;end if;
 end for;
 // This identity is of full lower germs, even if detL vanishes at s0.
 assert front*Vector(K,Eltseq(lower[q])) eq coeff*L;
 if #Keys(rr) gt 0 then Append(~C,rr);end if;
end for;
print "GERM_ROWS_ADDED",#C;

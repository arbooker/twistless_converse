// Export only exact reduced tables.  No mathematical condition is added.
Lres:=Matrix(K,[[Shift(IsDefined(A[i],j) select A[i][j] else K!0):j in free]:i in active]);
Jres:=Matrix(K,[[sources[j][i]:j in [1..#free]]:i in active]);
Craw:=Matrix(K,[[IsDefined(rr,j) select rr[j] else K!0:j in [1..#free]]:rr in C]);
path:="/tmp/level25_plus_poles_reduced.m";
Write(path,"K<x,y,z,w,a,b,c>:=RationalFunctionField(Rationals(),7);" : Overwrite:=true);
for item in [*<"Lres",Lres>,<"Jres",Jres>,<"Craw",Craw>*] do
 mat:=item[2];
 Write(path,item[1] cat ":=Matrix(K," cat IntegerToString(Nrows(mat)) cat "," cat IntegerToString(Ncols(mat)) cat "," cat Sprint(Eltseq(mat)) cat ");");
end for;
print "REDUCED_TABLES_SAVED",Nrows(Lres),Nrows(Craw),free;
quit;

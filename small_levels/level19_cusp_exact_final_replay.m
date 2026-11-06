SetNthreads(1);SetMemoryLimit(500000000);Alarm(45);SetQuitOnError(true);
SetOutputFile("/tmp/level19_cusp_exact_final_replay.log":Overwrite:=true);
PrintFile("/tmp/level19_cusp_exact_final_replay.completion.json","{\"completed\": false}":Overwrite:=true);
SetGBGlobalModular(false);assert not GetGBGlobalModular();
load "/tmp/level19_sparse_poles_compactall_fast.m";Old:=PP[1..15];
load "/tmp/level19_exact_membership_sparse_fast.m";
Old:=[Polynomial(Coefficients(p),[Monomial(S,Exponents(m)):m in Monomials(p)]):p in Old];
Inputs:=Old cat [PP[i]:i in [8,11,12,13,14,15]];assert #Inputs eq 21;
I:=ideal<S|Inputs>;
time GG:=GroebnerBasis(I:GlobalModular:=false,Homogenize:=false);
Expected:=[S|
(B+5)*(Y+1)*(X-1),
(Z-17)*(Y+1)*(X-1),
(Y-9)*(Y+1)*(X-1),
(X-4)*(Y+1)*(X-1),
A^2-3/5*Y*X+X^2+3/5*Y-13/5*X+8/5,
(A+X-1)*(Y+1)];
assert GG eq Expected;
assert &and[NormalForm(p,I) eq 0:p in Inputs];
h:=(Y+1)*(X-1);
assert h*(X-4) eq GG[4];
assert h*(A+3) eq (X-1)*GG[6]-GG[4];
assert h*(Y-9) eq GG[3];
assert h*(B+5) eq GG[1];
assert h*(Z-17) eq GG[2];
print "PASS_EXACT_21_INPUTS_TO_SIX_BASIS";
print "PASS_ORIGINAL_UNITS_ONLY_X4_A_MINUS3_Y9_B_MINUS5_Z17";
Write("/tmp/level19_cusp_exact_final_replay.basis",GG:Overwrite:=true);
PrintFile("/tmp/level19_cusp_exact_final_replay.completion.json","{\"completed\": true,\"returncode\": 0}":Overwrite:=true);
UnsetOutputFile();quit;

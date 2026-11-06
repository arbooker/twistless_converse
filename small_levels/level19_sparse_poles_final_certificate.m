// Standalone deterministic N19 equal-sign generic pole certificate.
SetNthreads(1);SetMemoryLimit(500000000);Alarm(45);SetQuitOnError(true);
SetOutputFile("/tmp/level19_sparse_poles_final_certificate.log":Overwrite:=true);
SetGBGlobalModular(false);assert not GetGBGlobalModular();
load "small_levels/level19_sparse_poles_final_data.m";
assert #Inputs eq 21;
I:=ideal<S|Inputs>;
time GG:=GroebnerBasis(I:GlobalModular:=false,Homogenize:=false);
unit:=(Y+1)*(X-1);
Expected:=[(B+5)*unit,(Z-17)*unit,(Y-9)*unit,(X-4)*unit,
 A^2-3/5*Y*X+X^2+3/5*Y-13/5*X+8/5,
 (Y+1)*(A+X-1)];
assert GG eq Expected;
assert ExactQuotient(GG[4],unit) eq X-4;
assert ExactQuotient(GG[6],Y+1)-ExactQuotient(GG[4],unit) eq A+3;
print "PASS: exact unsaturated rational basis and X=4,A=-3 identities",GG;
PrintFile("/tmp/level19_sparse_poles_final_certificate.pass","PASS deterministic rational certificate":Overwrite:=true);
PrintFile("/tmp/level19_sparse_poles_final_certificate_completion.json","{\"completed\":true,\"exit_status\":0,\"result\":\"PASS\"}":Overwrite:=true);quit;

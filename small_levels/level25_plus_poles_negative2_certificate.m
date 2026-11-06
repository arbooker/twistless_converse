// Six exact rows from the full primitive lower-germ certificate.
// Regenerate provenance with level25_plus_poles_negative2_prepare.py 2.
Alarm(45);SetMemoryLimit(500000000);SetNthreads(1);SetQuitOnError(true);
SetGBGlobalModular(false);
R<u,C,B,A,Z,W,Y,X,t>:=PolynomialRing(Rationals(),9,"grevlex");
P:=[
    A*Z*W*Y*X*t - 1,
    A^3*Y + A^2*X^2 + A^2*Y - A*Y*X - A*X^2 + A*X - Y*X - 2*X^2 + X,
    A*Y*X^3 - A*X^3 + A^2*Y - A*Y*X - Y^2*X + A*X^2 - Y*X^2 + 2*X^3 - 3*X^2 + X,
    -2*A^2*Y*X^3 + B*A^2*Y*X - 41/2*A^3*Y*X - 45/4*A^2*Y*X^2 + B*A*X^3 + 
        4*A^2*X^3 - 15/4*B*Y*X^3 - 77/8*A*Y*X^3 - 19*A^3*Y - 37*A^2*Y*X - 
        14/3*A*Y^2*X - 19*A^2*X^2 + 14*B*Y*X^2 + 55*A*Y*X^2 - 2*B*X^3 - 3*A*X^3 
        - 14*A^2*Y - 49*A*Y*X - 28/3*Y^2*X + B*X^2 + 28*A*X^2 + 23*Y*X^2 - 
        10*X^3 - 19*A*X + 210*Y*X + 33*X^2 - 14*X,
    -A^3*Y*X^4 - A^4*Y*X^2 - A^3*Y*X^3 + B*A*Y*X^4 - A*Y^2*X^4 + A^4*Y*X + 
        2*A^2*Y^2*X^2 + 2*A^3*X^3 - B*A*Y*X^3 - A*Y^2*X^3 - A^2*X^4 + 3*A*Y*X^4 
        - A^4*Y + A^3*Y*X + A^2*Y^2*X - A^3*X^2 - 3*A^2*Y*X^2 - 4*A^2*X^3 + 
        4*A*Y*X^3 - Y^2*X^3 - A*X^4 - 2*Y*X^4 + A^2*Y*X + 4*A^2*X^2 - A*Y*X^2 - 
        Y^2*X^2 + 2*Y*X^3 + 6*X^4 - A^2*X - 5*X^3 + X^2,
    3/8*A^2*Y*X^4 + A^3*Y^2*X + 123/32*A^3*Y*X^2 + 239/64*A^2*Y*X^3 - 
        15/32*A*Y^2*X^3 - 3/4*A^2*X^4 + 231/128*A*Y*X^4 + 1/2*A^3*Y^2 - 
        9/16*A^3*Y*X + 7/4*A^2*Y^2*X + 127/8*A^2*Y*X^2 - 1/8*A*Y^2*X^2 - 
        9/16*A^2*X^3 + 7/2*A*Y*X^3 + 9/16*A*X^4 - 9/8*A^2*Y*X + 7*A*Y^2*X + 
        223/16*A*Y*X^2 - 3/4*A*X^3 + 15/16*Y*X^3 + 15/8*X^4 + 1/2*A*Y*X - 
        9/16*A*X^2 + 9/8*Y*X^2 + 21/16*X^3 - 9/8*X^2
];
I:=ideal<R|P>;G:=GroebnerBasis(I:GlobalModular:=false);
assert G eq [R!1];print "PASS_NEGATIVE2_SIX_ROW_CERTIFICATE";

module
public import SmallLevelTwentySixPariIdentityIndexDataSeriesV4
public import SmallLevelTwentySixPariIdentityFamilyV4
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixPariFirstGcd
open SmallLevelPolynomialCoefficientCertificate

theorem input_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity017.p4 x y z w a b u=
      SmallLevelTwentySixPariIdentity020.p0 x y z w a b u := by
  calc
    SmallLevelTwentySixPariIdentity017.p4 x y z w a b u=
        SmallLevelTwentySixPariIdentity017.c4_0 x z w a b u := by
      simp only [SmallLevelTwentySixPariIdentity017.p4,
        SmallLevelTwentySixPariIdentity017.coefficients4,evaluate,mul_zero,add_zero]
    _=SmallLevelTwentySixPariIdentity020.p0 x y z w a b u := by
      unfold SmallLevelTwentySixPariIdentity017.c4_0 SmallLevelTwentySixPariIdentity020.p0
      ring

/-- The first gcd consequence uses only the row87 resultant. The multiplier
of the row88 resultant in this exact certificate is zero. -/
theorem first_gcd_zero (x y z w a b u : ℂ)
    (h : SmallLevelTwentySixPariIdentity017.p4 x y z w a b u=0) :
    SmallLevelTwentySixPariIdentity020.p4 x y z w a b u=0 := by
  have h0 : SmallLevelTwentySixPariIdentity020.p0 x y z w a b u=0 :=
    (input_binding x y z w a b u).symm.trans h
  have he:=SmallLevelTwentySixPariIdentity020.identity x y z w a b u
  rw [h0] at he
  simpa only [SmallLevelTwentySixPariIdentity020.p3,
    SmallLevelTwentySixPariIdentity020.p6,zero_mul,mul_zero,zero_add,add_zero] using he.symm

#print axioms input_binding
#print axioms first_gcd_zero
end SmallLevelTwentySixPariFirstGcd

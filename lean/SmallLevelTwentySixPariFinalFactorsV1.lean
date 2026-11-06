module
public import SmallLevelTwentySixPariIdentityIndexDataSeriesV4
public import SmallLevelTwentySixRootTheoryV4
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelTwentySixPariFinalFactors
open SmallLevelPolynomialCoefficientCertificate
def factor6 (x : ℂ) : ℂ := ((((((541*x+(437))*x+(-16365))*x+(22673))*x+(59254))*x+(-113160))*x+(43200))

def factor7 (x : ℂ) : ℂ := (((((((1*x+(-8))*x+(0))*x+(164))*x+(-529))*x+(204))*x+(1464))*x+(-1440))

def factor21 (x : ℂ) : ℂ := (((((((((((((((((((((42507*x+(-2287455))*x+(56204898))*x+(-799368290))*x+(7040303019))*x+(-37422732735))*x+(101916400200))*x+(-51152144976))*x+(223923442016))*x+(-4878241723952))*x+(11858436837568))*x+(8248093175424))*x+(33834758589440))*x+(-205869092786176))*x+(-280076895772672))*x+(120517409079296))*x+(3096781474758656))*x+(1100773507203072))*x+(-11390042305986560))*x+(7694405557288960))*x+(901909443510272))*x+(-1158189470973952))

theorem factorization (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariIdentity022.p4 x y z w a b u=
      (x-2)^11*(x-1)^7*x^17*(x+5)*(factor6 x)^3*(factor7 x)^2*factor21 x := by
  simp only [SmallLevelTwentySixPariIdentity022.p4,SmallLevelTwentySixPariIdentity022.coefficients4,evaluate,SmallLevelTwentySixPariIdentity022.c4_0,SmallLevelTwentySixPariIdentity022.c4_1,SmallLevelTwentySixPariIdentity022.c4_2,SmallLevelTwentySixPariIdentity022.c4_3,SmallLevelTwentySixPariIdentity022.c4_4,SmallLevelTwentySixPariIdentity022.c4_5,SmallLevelTwentySixPariIdentity022.c4_6,SmallLevelTwentySixPariIdentity022.c4_7,SmallLevelTwentySixPariIdentity022.c4_8,SmallLevelTwentySixPariIdentity022.c4_9,SmallLevelTwentySixPariIdentity022.c4_10,SmallLevelTwentySixPariIdentity022.c4_11,SmallLevelTwentySixPariIdentity022.c4_12,SmallLevelTwentySixPariIdentity022.c4_13,SmallLevelTwentySixPariIdentity022.c4_14,SmallLevelTwentySixPariIdentity022.c4_15,SmallLevelTwentySixPariIdentity022.c4_16,SmallLevelTwentySixPariIdentity022.c4_17,SmallLevelTwentySixPariIdentity022.c4_18,SmallLevelTwentySixPariIdentity022.c4_19,SmallLevelTwentySixPariIdentity022.c4_20,SmallLevelTwentySixPariIdentity022.c4_21,SmallLevelTwentySixPariIdentity022.c4_22,SmallLevelTwentySixPariIdentity022.c4_23,SmallLevelTwentySixPariIdentity022.c4_24,SmallLevelTwentySixPariIdentity022.c4_25,SmallLevelTwentySixPariIdentity022.c4_26,SmallLevelTwentySixPariIdentity022.c4_27,SmallLevelTwentySixPariIdentity022.c4_28,SmallLevelTwentySixPariIdentity022.c4_29,SmallLevelTwentySixPariIdentity022.c4_30,SmallLevelTwentySixPariIdentity022.c4_31,SmallLevelTwentySixPariIdentity022.c4_32,SmallLevelTwentySixPariIdentity022.c4_33,SmallLevelTwentySixPariIdentity022.c4_34,SmallLevelTwentySixPariIdentity022.c4_35,SmallLevelTwentySixPariIdentity022.c4_36,SmallLevelTwentySixPariIdentity022.c4_37,SmallLevelTwentySixPariIdentity022.c4_38,SmallLevelTwentySixPariIdentity022.c4_39,SmallLevelTwentySixPariIdentity022.c4_40,SmallLevelTwentySixPariIdentity022.c4_41,SmallLevelTwentySixPariIdentity022.c4_42,SmallLevelTwentySixPariIdentity022.c4_43,SmallLevelTwentySixPariIdentity022.c4_44,SmallLevelTwentySixPariIdentity022.c4_45,SmallLevelTwentySixPariIdentity022.c4_46,SmallLevelTwentySixPariIdentity022.c4_47,SmallLevelTwentySixPariIdentity022.c4_48,SmallLevelTwentySixPariIdentity022.c4_49,SmallLevelTwentySixPariIdentity022.c4_50,SmallLevelTwentySixPariIdentity022.c4_51,SmallLevelTwentySixPariIdentity022.c4_52,SmallLevelTwentySixPariIdentity022.c4_53,SmallLevelTwentySixPariIdentity022.c4_54,SmallLevelTwentySixPariIdentity022.c4_55,SmallLevelTwentySixPariIdentity022.c4_56,SmallLevelTwentySixPariIdentity022.c4_57,SmallLevelTwentySixPariIdentity022.c4_58,SmallLevelTwentySixPariIdentity022.c4_59,SmallLevelTwentySixPariIdentity022.c4_60,SmallLevelTwentySixPariIdentity022.c4_61,SmallLevelTwentySixPariIdentity022.c4_62,SmallLevelTwentySixPariIdentity022.c4_63,SmallLevelTwentySixPariIdentity022.c4_64,SmallLevelTwentySixPariIdentity022.c4_65,SmallLevelTwentySixPariIdentity022.c4_66,SmallLevelTwentySixPariIdentity022.c4_67,SmallLevelTwentySixPariIdentity022.c4_68,SmallLevelTwentySixPariIdentity022.c4_69,SmallLevelTwentySixPariIdentity022.c4_70,SmallLevelTwentySixPariIdentity022.c4_71,SmallLevelTwentySixPariIdentity022.c4_72,SmallLevelTwentySixPariIdentity022.c4_73,SmallLevelTwentySixPariIdentity022.c4_74,SmallLevelTwentySixPariIdentity022.c4_75,SmallLevelTwentySixPariIdentity022.c4_76,SmallLevelTwentySixPariIdentity022.c4_77,SmallLevelTwentySixPariIdentity022.c4_78,SmallLevelTwentySixPariIdentity022.c4_79,SmallLevelTwentySixPariIdentity022.c4_80,SmallLevelTwentySixPariIdentity022.c4_81,SmallLevelTwentySixPariIdentity022.c4_82,SmallLevelTwentySixPariIdentity022.c4_83,SmallLevelTwentySixPariIdentity022.c4_84,SmallLevelTwentySixPariIdentity022.c4_85,SmallLevelTwentySixPariIdentity022.c4_86,SmallLevelTwentySixPariIdentity022.c4_87,SmallLevelTwentySixPariIdentity022.c4_88,SmallLevelTwentySixPariIdentity022.c4_89,factor6,factor7,factor21]
  ring

/-- Exhaustive algebraic branches of the generic eliminant. Deriving the
eliminant from original rows and excluding the extra branches are separate steps. -/
theorem branches (x y z w a b u : ℂ)
    (h : SmallLevelTwentySixPariIdentity022.p4 x y z w a b u=0) :
    x=2 ∨ x=1 ∨ x=0 ∨ x= -5 ∨ factor6 x=0 ∨ factor7 x=0 ∨ factor21 x=0 := by
  by_contra hn
  push Not at hn
  obtain ⟨h2,h1,h0,h5,h6,h7,h21⟩:=hn
  have h5' : x+5≠0 := by
    intro he
    apply h5
    linear_combination he
  have hp := mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (pow_ne_zero 11 (sub_ne_zero.mpr h2))
        (pow_ne_zero 7 (sub_ne_zero.mpr h1))) (pow_ne_zero 17 h0)) h5')
      (pow_ne_zero 3 h6)) (pow_ne_zero 2 h7)) h21
  exact hp ((factorization x y z w a b u).symm.trans h)

#print axioms factorization
#print axioms branches

/-- Bind the surviving degree21 factor to the independently certified root polynomial. -/
theorem target_binding (x : ℂ) :
    factor21 x=42507*SmallLevelTwentySixRoot.p21.eval x := by
  norm_num [factor21,SmallLevelTwentySixRoot.p21,
    QuantitativeArithmeticComplexHornerBounds.eval_hornerPolynomial,
    QuantitativeArithmeticComplexHornerBounds.hornerValue,SmallLevelTwentySixRoot.pCoefficient]
  ring

theorem root_branch (x : ℂ) (h : factor21 x=0) : SmallLevelTwentySixRoot.p21.eval x=0 := by
  rw [target_binding] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

#print axioms target_binding
#print axioms root_branch
end SmallLevelTwentySixPariFinalFactors

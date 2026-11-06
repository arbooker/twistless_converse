module
public import QuantitativeArithmeticPolynomialHornerBridgeV1
public import SmallLevelTwentySixMMPPariTraceIndexSeriesV4
public import SmallLevelTwentySixMMPPariTraceIndexFamilySeriesV4
public import SmallLevelTwentySixPariFirstChartTheoryV4
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPQuadraticBranch
open SmallLevelPolynomialCoefficientCertificate
theorem low_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace046.p1 x y z w a b u =
    SmallLevelTwentySixPariFirstChart.lowCurve x y z w a b u := by rfl

theorem low_remainder (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace046.p4 x y z w a b u =
    SmallLevelTwentySixMMPPariTrace037.p1 x y z w a b u := by rfl

theorem first_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace047.p1 x y z w a b u = SmallLevelTwentySixMMPPariTrace019.p6 x y z w a b u := by
  unfold SmallLevelTwentySixMMPPariTrace047.p1
  rw [QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner]
  simp only [SmallLevelTwentySixMMPPariTrace047.coefficients1, QuantitativeArithmeticPolynomialHornerBridge.rightHorner, zero_mul, zero_add, SmallLevelTwentySixMMPPariTrace047.c1_0, SmallLevelTwentySixMMPPariTrace047.c1_1, SmallLevelTwentySixMMPPariTrace047.c1_2, SmallLevelTwentySixMMPPariTrace047.c1_3, SmallLevelTwentySixMMPPariTrace047.c1_4, SmallLevelTwentySixMMPPariTrace047.c1_5, SmallLevelTwentySixMMPPariTrace047.c1_6, SmallLevelTwentySixMMPPariTrace047.c1_7, SmallLevelTwentySixMMPPariTrace047.c1_8, SmallLevelTwentySixMMPPariTrace047.c1_9, SmallLevelTwentySixMMPPariTrace047.c1_10, SmallLevelTwentySixMMPPariTrace047.c1_11, SmallLevelTwentySixMMPPariTrace047.c1_12, SmallLevelTwentySixMMPPariTrace047.c1_13, SmallLevelTwentySixMMPPariTrace047.c1_14, SmallLevelTwentySixMMPPariTrace047.c1_15, SmallLevelTwentySixMMPPariTrace047.c1_16, SmallLevelTwentySixMMPPariTrace047.c1_17, SmallLevelTwentySixMMPPariTrace047.c1_18, SmallLevelTwentySixMMPPariTrace047.c1_19, SmallLevelTwentySixMMPPariTrace047.c1_20, SmallLevelTwentySixMMPPariTrace047.c1_21, SmallLevelTwentySixMMPPariTrace047.c1_22, SmallLevelTwentySixMMPPariTrace047.c1_23, SmallLevelTwentySixMMPPariTrace047.c1_24, SmallLevelTwentySixMMPPariTrace047.c1_25, SmallLevelTwentySixMMPPariTrace047.c1_26, SmallLevelTwentySixMMPPariTrace047.c1_27, SmallLevelTwentySixMMPPariTrace047.c1_28, SmallLevelTwentySixMMPPariTrace047.c1_29, SmallLevelTwentySixMMPPariTrace047.c1_30, SmallLevelTwentySixMMPPariTrace047.c1_31, SmallLevelTwentySixMMPPariTrace047.c1_32, SmallLevelTwentySixMMPPariTrace019.p6, SmallLevelTwentySixMMPPariTrace019.p1]

theorem first_remainder (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace047.p4 x y z w a b u = SmallLevelTwentySixMMPPariTrace037.p3 x y z w a b u := by
  simp only [SmallLevelTwentySixMMPPariTrace047.p4, SmallLevelTwentySixMMPPariTrace047.coefficients4, SmallLevelTwentySixMMPPariTrace047.c4_0, SmallLevelTwentySixMMPPariTrace047.c4_1, evaluate, mul_zero, add_zero, mul_one, one_mul, SmallLevelTwentySixMMPPariTrace037.p3]
  try ac_rfl

theorem first_zero (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace047.p2 x y z w a b u = 0 := by
  simp only [SmallLevelTwentySixMMPPariTrace047.p2, SmallLevelTwentySixMMPPariTrace047.coefficients2, evaluate, mul_zero, add_zero, mul_one, one_mul]
  try ac_rfl

theorem first_modulus (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace047.p5 x y z w a b u = x^2-5*x+8 := by
  simp only [SmallLevelTwentySixMMPPariTrace047.p5, SmallLevelTwentySixMMPPariTrace047.coefficients5, SmallLevelTwentySixMMPPariTrace047.c5_0, SmallLevelTwentySixMMPPariTrace047.c5_1, SmallLevelTwentySixMMPPariTrace047.c5_2, evaluate, mul_zero, add_zero, mul_one, one_mul]
  ring

/-- Exact reduction of the quadratic branch; only the first source is needed. -/
theorem y_eq_nine (x y z w a b u : ℂ)
    (hlow : SmallLevelTwentySixPariFirstChart.lowCurve x y z w a b u = 0)
    (hfirst : SmallLevelTwentySixMMPPariTrace019.p6 x y z w a b u = 0)
    (hq : x^2-5*x+8=0) : y=9 := by
  have hq46 : SmallLevelTwentySixMMPPariTrace046.p5 x y z w a b u = 0 := by
    dsimp [SmallLevelTwentySixMMPPariTrace046.p5]
    linear_combination hq
  have hq37 : SmallLevelTwentySixMMPPariTrace037.p5 x y z w a b u = 0 := hq46
  have hl : SmallLevelTwentySixMMPPariTrace037.p1 x y z w a b u = 0 := by
    have hi := SmallLevelTwentySixMMPPariTrace046.identity x y z w a b u
    rw [low_binding, hlow, low_remainder, hq46] at hi
    simpa only [SmallLevelTwentySixMMPPariTrace046.p2, zero_mul, mul_zero, zero_add, add_zero] using hi.symm
  have hr : SmallLevelTwentySixMMPPariTrace037.p3 x y z w a b u = 0 := by
    have hi := SmallLevelTwentySixMMPPariTrace047.identity x y z w a b u
    rw [first_binding, hfirst, first_zero, first_remainder, first_modulus, hq] at hi
    simpa only [zero_mul, mul_zero, zero_add, add_zero] using hi.symm
  have hi := SmallLevelTwentySixMMPPariTrace037.identity x y z w a b u
  rw [hl, hr, hq37] at hi
  have ht : SmallLevelTwentySixMMPPariTrace037.p4 x y z w a b u = 0 := by
    simpa only [zero_mul, mul_zero, zero_add, add_zero] using hi.symm
  dsimp [SmallLevelTwentySixMMPPariTrace037.p4] at ht
  linear_combination ht

#print axioms y_eq_nine
end QuantitativeArithmeticSmallLevelTwentySixMMPQuadraticBranch

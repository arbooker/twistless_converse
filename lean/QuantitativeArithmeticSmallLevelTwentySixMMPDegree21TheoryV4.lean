module

public import QuantitativeArithmeticPolynomialHornerBridgeV1
public import SmallLevelTwentySixMMPPariTraceIndexFamilySeriesV4
public import SmallLevelTwentySixMMPPariTraceIndexSeriesV4
public import SmallLevelTwentySixPariFinalFactorsV1
public import SmallLevelTwentySixPariFirstChartTheoryV4
public import SmallLevelTwentySixRootTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySixMMPDegree21. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySixMMPDegree21BindingsV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPDegree21
open SmallLevelPolynomialCoefficientCertificate

/- Exact source bindings for the degree 21 branch. No source equation or
polynomial identity is assumed in these lemmas. -/
theorem low_input_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace049.p1 x y z w a b u =
      SmallLevelTwentySixPariFirstChart.lowCurve x y z w a b u := by
  rfl

theorem low_remainder_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace040.p1 x y z w a b u =
      SmallLevelTwentySixMMPPariTrace049.p4 x y z w a b u := by
  unfold SmallLevelTwentySixMMPPariTrace040.p1
  rw [QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner]
  simp only [SmallLevelTwentySixMMPPariTrace040.coefficients1, QuantitativeArithmeticPolynomialHornerBridge.rightHorner, zero_mul, zero_add, SmallLevelTwentySixMMPPariTrace040.c1_0, SmallLevelTwentySixMMPPariTrace040.c1_1, SmallLevelTwentySixMMPPariTrace040.c1_2, SmallLevelTwentySixMMPPariTrace040.c1_3, SmallLevelTwentySixMMPPariTrace040.c1_4, SmallLevelTwentySixMMPPariTrace040.c1_5, SmallLevelTwentySixMMPPariTrace040.c1_6, SmallLevelTwentySixMMPPariTrace040.c1_7, SmallLevelTwentySixMMPPariTrace040.c1_8, SmallLevelTwentySixMMPPariTrace040.c1_9, SmallLevelTwentySixMMPPariTrace049.p4]

theorem first_input_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace050.p1 x y z w a b u =
      SmallLevelTwentySixMMPPariTrace019.p6 x y z w a b u := by
  unfold SmallLevelTwentySixMMPPariTrace050.p1
  rw [QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner]
  simp only [SmallLevelTwentySixMMPPariTrace050.coefficients1, QuantitativeArithmeticPolynomialHornerBridge.rightHorner, zero_mul, zero_add, SmallLevelTwentySixMMPPariTrace050.c1_0, SmallLevelTwentySixMMPPariTrace050.c1_1, SmallLevelTwentySixMMPPariTrace050.c1_2, SmallLevelTwentySixMMPPariTrace050.c1_3, SmallLevelTwentySixMMPPariTrace050.c1_4, SmallLevelTwentySixMMPPariTrace050.c1_5, SmallLevelTwentySixMMPPariTrace050.c1_6, SmallLevelTwentySixMMPPariTrace050.c1_7, SmallLevelTwentySixMMPPariTrace050.c1_8, SmallLevelTwentySixMMPPariTrace050.c1_9, SmallLevelTwentySixMMPPariTrace050.c1_10, SmallLevelTwentySixMMPPariTrace050.c1_11, SmallLevelTwentySixMMPPariTrace050.c1_12, SmallLevelTwentySixMMPPariTrace050.c1_13, SmallLevelTwentySixMMPPariTrace050.c1_14, SmallLevelTwentySixMMPPariTrace050.c1_15, SmallLevelTwentySixMMPPariTrace050.c1_16, SmallLevelTwentySixMMPPariTrace050.c1_17, SmallLevelTwentySixMMPPariTrace050.c1_18, SmallLevelTwentySixMMPPariTrace050.c1_19, SmallLevelTwentySixMMPPariTrace050.c1_20, SmallLevelTwentySixMMPPariTrace050.c1_21, SmallLevelTwentySixMMPPariTrace050.c1_22, SmallLevelTwentySixMMPPariTrace050.c1_23, SmallLevelTwentySixMMPPariTrace050.c1_24, SmallLevelTwentySixMMPPariTrace050.c1_25, SmallLevelTwentySixMMPPariTrace050.c1_26, SmallLevelTwentySixMMPPariTrace050.c1_27, SmallLevelTwentySixMMPPariTrace050.c1_28, SmallLevelTwentySixMMPPariTrace050.c1_29, SmallLevelTwentySixMMPPariTrace050.c1_30, SmallLevelTwentySixMMPPariTrace050.c1_31, SmallLevelTwentySixMMPPariTrace050.c1_32, SmallLevelTwentySixMMPPariTrace019.p6, SmallLevelTwentySixMMPPariTrace019.p1]

theorem first_remainder_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace040.p3 x y z w a b u =
      SmallLevelTwentySixMMPPariTrace050.p4 x y z w a b u := by
  rfl

theorem first_zero_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace050.p2 x y z w a b u =
      0 := by
  rfl

theorem modulus_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace040.p5 x y z w a b u =
      SmallLevelTwentySixPariFinalFactors.factor21 x := by
  unfold SmallLevelTwentySixMMPPariTrace040.p5
  rw [QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner]
  simp only [SmallLevelTwentySixMMPPariTrace040.coefficients5, QuantitativeArithmeticPolynomialHornerBridge.rightHorner, zero_mul, zero_add, SmallLevelTwentySixMMPPariTrace040.c5_0, SmallLevelTwentySixMMPPariTrace040.c5_1, SmallLevelTwentySixMMPPariTrace040.c5_2, SmallLevelTwentySixMMPPariTrace040.c5_3, SmallLevelTwentySixMMPPariTrace040.c5_4, SmallLevelTwentySixMMPPariTrace040.c5_5, SmallLevelTwentySixMMPPariTrace040.c5_6, SmallLevelTwentySixMMPPariTrace040.c5_7, SmallLevelTwentySixMMPPariTrace040.c5_8, SmallLevelTwentySixMMPPariTrace040.c5_9, SmallLevelTwentySixMMPPariTrace040.c5_10, SmallLevelTwentySixMMPPariTrace040.c5_11, SmallLevelTwentySixMMPPariTrace040.c5_12, SmallLevelTwentySixMMPPariTrace040.c5_13, SmallLevelTwentySixMMPPariTrace040.c5_14, SmallLevelTwentySixMMPPariTrace040.c5_15, SmallLevelTwentySixMMPPariTrace040.c5_16, SmallLevelTwentySixMMPPariTrace040.c5_17, SmallLevelTwentySixMMPPariTrace040.c5_18, SmallLevelTwentySixMMPPariTrace040.c5_19, SmallLevelTwentySixMMPPariTrace040.c5_20, SmallLevelTwentySixMMPPariTrace040.c5_21, SmallLevelTwentySixPariFinalFactors.factor21]

theorem input_modulus_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace050.p5 x y z w a b u =
      SmallLevelTwentySixPariFinalFactors.factor21 x := by
  exact modulus_binding x y z w a b u

theorem endpoint_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace040.p4 x y z w a b u =
      SmallLevelTwentySixMMPPariTrace042.p1 x y z w a b u := by
  unfold SmallLevelTwentySixMMPPariTrace040.p4
  rw [QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner]
  simp only [SmallLevelTwentySixMMPPariTrace040.coefficients4, QuantitativeArithmeticPolynomialHornerBridge.rightHorner, zero_mul, zero_add, SmallLevelTwentySixMMPPariTrace040.c4_0, SmallLevelTwentySixMMPPariTrace040.c4_1, SmallLevelTwentySixMMPPariTrace040.c4_2, SmallLevelTwentySixMMPPariTrace040.c4_3, SmallLevelTwentySixMMPPariTrace040.c4_4, SmallLevelTwentySixMMPPariTrace040.c4_5, SmallLevelTwentySixMMPPariTrace040.c4_6, SmallLevelTwentySixMMPPariTrace040.c4_7, SmallLevelTwentySixMMPPariTrace040.c4_8, SmallLevelTwentySixMMPPariTrace040.c4_9, SmallLevelTwentySixMMPPariTrace040.c4_10, SmallLevelTwentySixMMPPariTrace040.c4_11, SmallLevelTwentySixMMPPariTrace040.c4_12, SmallLevelTwentySixMMPPariTrace040.c4_13, SmallLevelTwentySixMMPPariTrace040.c4_14, SmallLevelTwentySixMMPPariTrace040.c4_15, SmallLevelTwentySixMMPPariTrace040.c4_16, SmallLevelTwentySixMMPPariTrace040.c4_17, SmallLevelTwentySixMMPPariTrace040.c4_18, SmallLevelTwentySixMMPPariTrace040.c4_19, SmallLevelTwentySixMMPPariTrace040.c4_20, SmallLevelTwentySixMMPPariTrace042.p1]

theorem target_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace042.p1 x y z w a b u =
      y - SmallLevelTwentySixRoot.q20.eval x := by
  norm_num [SmallLevelTwentySixMMPPariTrace042.p1, SmallLevelTwentySixRoot.q20,
    QuantitativeArithmeticComplexHornerBounds.eval_hornerPolynomial,
    QuantitativeArithmeticComplexHornerBounds.hornerValue,
    SmallLevelTwentySixRoot.qCoefficient]
  ring

end QuantitativeArithmeticSmallLevelTwentySixMMPDegree21
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySixMMPDegree21V1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPDegree21

/-- The first branch gcd already yields the interpolation relation.
The second reduced source equation is unnecessary for this branch. -/
theorem root_relation_of_first (x y z w a b u : ℂ)
    (hlow : SmallLevelTwentySixPariFirstChart.lowCurve x y z w a b u = 0)
    (hfirst : SmallLevelTwentySixMMPPariTrace019.p6 x y z w a b u = 0)
    (hfactor : SmallLevelTwentySixPariFinalFactors.factor21 x = 0) :
    SmallLevelTwentySixRoot.q20.eval x = y := by
  have hlow' : SmallLevelTwentySixMMPPariTrace040.p1 x y z w a b u = 0 := by
    rw [low_remainder_binding]
    exact hlow
  have hfirst' : SmallLevelTwentySixMMPPariTrace040.p3 x y z w a b u = 0 := by
    rw [first_remainder_binding]
    have hi := SmallLevelTwentySixMMPPariTrace050.identity x y z w a b u
    rw [first_input_binding, hfirst, first_zero_binding, input_modulus_binding,
      hfactor] at hi
    simpa only [mul_zero, zero_mul, zero_add, add_zero] using hi.symm
  have hi := SmallLevelTwentySixMMPPariTrace040.identity x y z w a b u
  rw [hlow', hfirst', modulus_binding, hfactor] at hi
  have hout : SmallLevelTwentySixMMPPariTrace040.p4 x y z w a b u = 0 := by
    simpa only [mul_zero, zero_mul, zero_add, add_zero] using hi.symm
  rw [endpoint_binding, target_binding] at hout
  exact (sub_eq_zero.mp hout).symm

/-- Interface for the two-source elimination chain. -/
theorem root_relation (x y z w a b u : ℂ)
    (hlow : SmallLevelTwentySixPariFirstChart.lowCurve x y z w a b u = 0)
    (hfirst : SmallLevelTwentySixMMPPariTrace019.p6 x y z w a b u = 0)
    (_hsecond : SmallLevelTwentySixMMPPariTrace031.p6 x y z w a b u = 0)
    (hfactor : SmallLevelTwentySixPariFinalFactors.factor21 x = 0) :
    SmallLevelTwentySixRoot.q20.eval x = y :=
  root_relation_of_first x y z w a b u hlow hfirst hfactor

#print axioms root_relation_of_first
#print axioms root_relation
end QuantitativeArithmeticSmallLevelTwentySixMMPDegree21
end
end

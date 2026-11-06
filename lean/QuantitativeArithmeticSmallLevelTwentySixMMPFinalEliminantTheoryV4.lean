module

public import QuantitativeArithmeticPolynomialHornerBridgeV1
public import SmallLevelTwentySixMMPPariTraceIndexFamilySeriesV4
public import SmallLevelTwentySixMMPPariTraceIndexSeriesV4
public import SmallLevelTwentySixPariFinalFactorsV1
public import SmallLevelTwentySixPariFirstChartTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySixMMPFinalEliminant. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySixMMPFinalEliminantBindingsV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPFinalEliminant
open SmallLevelPolynomialCoefficientCertificate

/- Exact data bindings for the two resultant certificates and their gcd. -/
theorem first_low_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace020.p1 x y z w a b u =
      SmallLevelTwentySixPariFirstChart.lowCurve x y z w a b u := by
  unfold SmallLevelTwentySixMMPPariTrace020.p1
  rw [QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner]
  simp only [SmallLevelTwentySixMMPPariTrace020.coefficients1, SmallLevelTwentySixMMPPariTrace020.c1_0, SmallLevelTwentySixMMPPariTrace020.c1_1, SmallLevelTwentySixMMPPariTrace020.c1_2, SmallLevelTwentySixMMPPariTrace020.c1_3, SmallLevelTwentySixMMPPariTrace020.c1_4, SmallLevelTwentySixMMPPariTrace020.c1_5, SmallLevelTwentySixMMPPariTrace020.c1_6, SmallLevelTwentySixMMPPariTrace020.c1_7, SmallLevelTwentySixMMPPariTrace020.c1_8, SmallLevelTwentySixMMPPariTrace020.c1_9, QuantitativeArithmeticPolynomialHornerBridge.rightHorner, zero_mul, zero_add, mul_zero, add_zero, mul_one, one_mul, SmallLevelTwentySixPariFirstChart.lowCurve,
    SmallLevelTwentySixPariIdentity007.p1]

theorem second_low_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace032.p1 x y z w a b u =
      SmallLevelTwentySixPariFirstChart.lowCurve x y z w a b u := by
  exact first_low_binding x y z w a b u

theorem first_source_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace020.p3 x y z w a b u =
      SmallLevelTwentySixMMPPariTrace019.p6 x y z w a b u := by
  unfold SmallLevelTwentySixMMPPariTrace020.p3
  rw [QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner]
  simp only [SmallLevelTwentySixMMPPariTrace020.coefficients3, SmallLevelTwentySixMMPPariTrace020.c3_0, SmallLevelTwentySixMMPPariTrace020.c3_1, SmallLevelTwentySixMMPPariTrace020.c3_2, SmallLevelTwentySixMMPPariTrace020.c3_3, SmallLevelTwentySixMMPPariTrace020.c3_4, SmallLevelTwentySixMMPPariTrace020.c3_5, SmallLevelTwentySixMMPPariTrace020.c3_6, SmallLevelTwentySixMMPPariTrace020.c3_7, SmallLevelTwentySixMMPPariTrace020.c3_8, SmallLevelTwentySixMMPPariTrace020.c3_9, SmallLevelTwentySixMMPPariTrace020.c3_10, SmallLevelTwentySixMMPPariTrace020.c3_11, SmallLevelTwentySixMMPPariTrace020.c3_12, SmallLevelTwentySixMMPPariTrace020.c3_13, SmallLevelTwentySixMMPPariTrace020.c3_14, SmallLevelTwentySixMMPPariTrace020.c3_15, SmallLevelTwentySixMMPPariTrace020.c3_16, SmallLevelTwentySixMMPPariTrace020.c3_17, SmallLevelTwentySixMMPPariTrace020.c3_18, SmallLevelTwentySixMMPPariTrace020.c3_19, SmallLevelTwentySixMMPPariTrace020.c3_20, SmallLevelTwentySixMMPPariTrace020.c3_21, SmallLevelTwentySixMMPPariTrace020.c3_22, SmallLevelTwentySixMMPPariTrace020.c3_23, SmallLevelTwentySixMMPPariTrace020.c3_24, SmallLevelTwentySixMMPPariTrace020.c3_25, SmallLevelTwentySixMMPPariTrace020.c3_26, SmallLevelTwentySixMMPPariTrace020.c3_27, SmallLevelTwentySixMMPPariTrace020.c3_28, SmallLevelTwentySixMMPPariTrace020.c3_29, SmallLevelTwentySixMMPPariTrace020.c3_30, SmallLevelTwentySixMMPPariTrace020.c3_31, SmallLevelTwentySixMMPPariTrace020.c3_32, QuantitativeArithmeticPolynomialHornerBridge.rightHorner, zero_mul, zero_add, mul_zero, add_zero, mul_one, one_mul, SmallLevelTwentySixMMPPariTrace019.p6, SmallLevelTwentySixMMPPariTrace019.p1]

theorem first_result_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace033.p1 x y z w a b u =
      SmallLevelTwentySixMMPPariTrace020.p4 x y z w a b u := by
  rfl

theorem second_source_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace032.p3 x y z w a b u =
      SmallLevelTwentySixMMPPariTrace031.p6 x y z w a b u := by
  unfold SmallLevelTwentySixMMPPariTrace032.p3
  rw [QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner]
  simp only [SmallLevelTwentySixMMPPariTrace032.coefficients3, SmallLevelTwentySixMMPPariTrace032.c3_0, SmallLevelTwentySixMMPPariTrace032.c3_1, SmallLevelTwentySixMMPPariTrace032.c3_2, SmallLevelTwentySixMMPPariTrace032.c3_3, SmallLevelTwentySixMMPPariTrace032.c3_4, SmallLevelTwentySixMMPPariTrace032.c3_5, SmallLevelTwentySixMMPPariTrace032.c3_6, SmallLevelTwentySixMMPPariTrace032.c3_7, SmallLevelTwentySixMMPPariTrace032.c3_8, SmallLevelTwentySixMMPPariTrace032.c3_9, SmallLevelTwentySixMMPPariTrace032.c3_10, SmallLevelTwentySixMMPPariTrace032.c3_11, SmallLevelTwentySixMMPPariTrace032.c3_12, SmallLevelTwentySixMMPPariTrace032.c3_13, SmallLevelTwentySixMMPPariTrace032.c3_14, SmallLevelTwentySixMMPPariTrace032.c3_15, SmallLevelTwentySixMMPPariTrace032.c3_16, SmallLevelTwentySixMMPPariTrace032.c3_17, SmallLevelTwentySixMMPPariTrace032.c3_18, SmallLevelTwentySixMMPPariTrace032.c3_19, SmallLevelTwentySixMMPPariTrace032.c3_20, SmallLevelTwentySixMMPPariTrace032.c3_21, SmallLevelTwentySixMMPPariTrace032.c3_22, SmallLevelTwentySixMMPPariTrace032.c3_23, SmallLevelTwentySixMMPPariTrace032.c3_24, SmallLevelTwentySixMMPPariTrace032.c3_25, SmallLevelTwentySixMMPPariTrace032.c3_26, SmallLevelTwentySixMMPPariTrace032.c3_27, SmallLevelTwentySixMMPPariTrace032.c3_28, SmallLevelTwentySixMMPPariTrace032.c3_29, SmallLevelTwentySixMMPPariTrace032.c3_30, SmallLevelTwentySixMMPPariTrace032.c3_31, SmallLevelTwentySixMMPPariTrace032.c3_32, SmallLevelTwentySixMMPPariTrace032.c3_33, SmallLevelTwentySixMMPPariTrace032.c3_34, SmallLevelTwentySixMMPPariTrace032.c3_35, SmallLevelTwentySixMMPPariTrace032.c3_36, SmallLevelTwentySixMMPPariTrace032.c3_37, SmallLevelTwentySixMMPPariTrace032.c3_38, SmallLevelTwentySixMMPPariTrace032.c3_39, SmallLevelTwentySixMMPPariTrace032.c3_40, SmallLevelTwentySixMMPPariTrace032.c3_41, QuantitativeArithmeticPolynomialHornerBridge.rightHorner, zero_mul, zero_add, mul_zero, add_zero, mul_one, one_mul, SmallLevelTwentySixMMPPariTrace031.p6, SmallLevelTwentySixMMPPariTrace031.p1]

theorem second_result_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace033.p3 x y z w a b u =
      SmallLevelTwentySixMMPPariTrace032.p4 x y z w a b u := by
  rfl

theorem first_zero_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace020.p5 x y z w a b u =
      0 := by
  rfl

theorem second_zero_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace032.p5 x y z w a b u =
      0 := by
  rfl

theorem gcd_zero_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace033.p5 x y z w a b u =
      0 := by
  rfl

end QuantitativeArithmeticSmallLevelTwentySixMMPFinalEliminant
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySixMMPFinalEliminantFactorizationV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPFinalEliminant
open SmallLevelPolynomialCoefficientCertificate

open SmallLevelTwentySixPariFinalFactors

/-- The primitive gcd is exactly the product of the existing physical branch factors. -/
theorem factorization (x y z w a b u : ℂ) :
    SmallLevelTwentySixMMPPariTrace033.p4 x y z w a b u =
      x^2*(x-2)^7*(x-1)^6*(x^2-5*x+8)*(factor6 x)^2*(factor7 x)^2*factor21 x := by
  simp only [SmallLevelTwentySixMMPPariTrace033.p4, SmallLevelTwentySixMMPPariTrace033.coefficients4, SmallLevelTwentySixMMPPariTrace033.c4_0, SmallLevelTwentySixMMPPariTrace033.c4_1, SmallLevelTwentySixMMPPariTrace033.c4_2, SmallLevelTwentySixMMPPariTrace033.c4_3, SmallLevelTwentySixMMPPariTrace033.c4_4, SmallLevelTwentySixMMPPariTrace033.c4_5, SmallLevelTwentySixMMPPariTrace033.c4_6, SmallLevelTwentySixMMPPariTrace033.c4_7, SmallLevelTwentySixMMPPariTrace033.c4_8, SmallLevelTwentySixMMPPariTrace033.c4_9, SmallLevelTwentySixMMPPariTrace033.c4_10, SmallLevelTwentySixMMPPariTrace033.c4_11, SmallLevelTwentySixMMPPariTrace033.c4_12, SmallLevelTwentySixMMPPariTrace033.c4_13, SmallLevelTwentySixMMPPariTrace033.c4_14, SmallLevelTwentySixMMPPariTrace033.c4_15, SmallLevelTwentySixMMPPariTrace033.c4_16, SmallLevelTwentySixMMPPariTrace033.c4_17, SmallLevelTwentySixMMPPariTrace033.c4_18, SmallLevelTwentySixMMPPariTrace033.c4_19, SmallLevelTwentySixMMPPariTrace033.c4_20, SmallLevelTwentySixMMPPariTrace033.c4_21, SmallLevelTwentySixMMPPariTrace033.c4_22, SmallLevelTwentySixMMPPariTrace033.c4_23, SmallLevelTwentySixMMPPariTrace033.c4_24, SmallLevelTwentySixMMPPariTrace033.c4_25, SmallLevelTwentySixMMPPariTrace033.c4_26, SmallLevelTwentySixMMPPariTrace033.c4_27, SmallLevelTwentySixMMPPariTrace033.c4_28, SmallLevelTwentySixMMPPariTrace033.c4_29, SmallLevelTwentySixMMPPariTrace033.c4_30, SmallLevelTwentySixMMPPariTrace033.c4_31, SmallLevelTwentySixMMPPariTrace033.c4_32, SmallLevelTwentySixMMPPariTrace033.c4_33, SmallLevelTwentySixMMPPariTrace033.c4_34, SmallLevelTwentySixMMPPariTrace033.c4_35, SmallLevelTwentySixMMPPariTrace033.c4_36, SmallLevelTwentySixMMPPariTrace033.c4_37, SmallLevelTwentySixMMPPariTrace033.c4_38, SmallLevelTwentySixMMPPariTrace033.c4_39, SmallLevelTwentySixMMPPariTrace033.c4_40, SmallLevelTwentySixMMPPariTrace033.c4_41, SmallLevelTwentySixMMPPariTrace033.c4_42, SmallLevelTwentySixMMPPariTrace033.c4_43, SmallLevelTwentySixMMPPariTrace033.c4_44, SmallLevelTwentySixMMPPariTrace033.c4_45, SmallLevelTwentySixMMPPariTrace033.c4_46, SmallLevelTwentySixMMPPariTrace033.c4_47, SmallLevelTwentySixMMPPariTrace033.c4_48, SmallLevelTwentySixMMPPariTrace033.c4_49, SmallLevelTwentySixMMPPariTrace033.c4_50, SmallLevelTwentySixMMPPariTrace033.c4_51, SmallLevelTwentySixMMPPariTrace033.c4_52, SmallLevelTwentySixMMPPariTrace033.c4_53, SmallLevelTwentySixMMPPariTrace033.c4_54, SmallLevelTwentySixMMPPariTrace033.c4_55, SmallLevelTwentySixMMPPariTrace033.c4_56, SmallLevelTwentySixMMPPariTrace033.c4_57, SmallLevelTwentySixMMPPariTrace033.c4_58, SmallLevelTwentySixMMPPariTrace033.c4_59, SmallLevelTwentySixMMPPariTrace033.c4_60, SmallLevelTwentySixMMPPariTrace033.c4_61, SmallLevelTwentySixMMPPariTrace033.c4_62, SmallLevelTwentySixMMPPariTrace033.c4_63, SmallLevelTwentySixMMPPariTrace033.c4_64, evaluate, mul_zero, add_zero, mul_one, one_mul, factor6, factor7, factor21]
  ring

#print axioms factorization
end QuantitativeArithmeticSmallLevelTwentySixMMPFinalEliminant
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySixMMPFinalEliminantV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPFinalEliminant
open SmallLevelPolynomialCoefficientCertificate

open SmallLevelTwentySixPariFinalFactors

theorem first_resultant_zero (x y z w a b u : ℂ)
    (hlow : SmallLevelTwentySixPariFirstChart.lowCurve x y z w a b u = 0)
    (hsource : SmallLevelTwentySixMMPPariTrace019.p6 x y z w a b u = 0) :
    SmallLevelTwentySixMMPPariTrace020.p4 x y z w a b u = 0 := by
  have hi := SmallLevelTwentySixMMPPariTrace020.identity x y z w a b u
  rw [first_low_binding, hlow, first_source_binding, hsource,
    first_zero_binding] at hi
  simpa only [mul_zero, zero_mul, zero_add, add_zero] using hi.symm

theorem second_resultant_zero (x y z w a b u : ℂ)
    (hlow : SmallLevelTwentySixPariFirstChart.lowCurve x y z w a b u = 0)
    (hsource : SmallLevelTwentySixMMPPariTrace031.p6 x y z w a b u = 0) :
    SmallLevelTwentySixMMPPariTrace032.p4 x y z w a b u = 0 := by
  have hi := SmallLevelTwentySixMMPPariTrace032.identity x y z w a b u
  rw [second_low_binding, hlow, second_source_binding, hsource,
    second_zero_binding] at hi
  simpa only [mul_zero, zero_mul, zero_add, add_zero] using hi.symm

/-- The two reduced source equations and the old low curve force the final
factorized eliminant. Their derivation from analytic data is a separate theorem. -/
theorem eliminant_zero (x y z w a b u : ℂ)
    (hlow : SmallLevelTwentySixPariFirstChart.lowCurve x y z w a b u = 0)
    (hfirst : SmallLevelTwentySixMMPPariTrace019.p6 x y z w a b u = 0)
    (hsecond : SmallLevelTwentySixMMPPariTrace031.p6 x y z w a b u = 0) :
    x^2*(x-2)^7*(x-1)^6*(x^2-5*x+8)*(factor6 x)^2*(factor7 x)^2*factor21 x = 0 := by
  have hfirst' := first_resultant_zero x y z w a b u hlow hfirst
  have hsecond' := second_resultant_zero x y z w a b u hlow hsecond
  have hi := SmallLevelTwentySixMMPPariTrace033.identity x y z w a b u
  rw [first_result_binding, hfirst', second_result_binding, hsecond',
    gcd_zero_binding] at hi
  have hout : SmallLevelTwentySixMMPPariTrace033.p4 x y z w a b u = 0 := by
    simpa only [mul_zero, zero_mul, zero_add, add_zero] using hi.symm
  exact (factorization x y z w a b u).symm.trans hout

#print axioms first_resultant_zero
#print axioms second_resultant_zero
#print axioms eliminant_zero
end QuantitativeArithmeticSmallLevelTwentySixMMPFinalEliminant
end
end

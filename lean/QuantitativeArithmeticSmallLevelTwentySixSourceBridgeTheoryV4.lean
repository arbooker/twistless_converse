module

public import QuantitativeArithmeticSmallLevelTwentySixSourcePivot89TheoryV4
public import QuantitativeArithmeticSmallLevelTwentySixSourceW89TheoryV4
public import SmallLevelTwentySixPariIdentityFamilyV4
public import SmallLevelTwentySixPariSourcePivotIndexDataSeriesV4
public import SmallLevelTwentySixPariSourcePivotsTheoryV4
public import SmallLevelTwentySixPariSourcePolynomialIndexDataSeriesV4
public import SmallLevelTwentySixSourceResultantIndexDataSeriesV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySixSourceBridge. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySixSourcePivot89FourBindingV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixSourceBridge
theorem pivot89Four_binding (x y z w a b u : ℂ) :
    QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.p0 x y z w a b u=SmallLevelTwentySixPariSourcePivots.source4 x y z w a b u := by
  simp only [QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.p0,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.coefficients0,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c0_0,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c0_1,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c0_2,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c0_3,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c0_4,SmallLevelTwentySixPariSourcePivots.source4,SmallLevelPolynomialCoefficientCertificate.evaluate]
  first | rfl | ac_rfl | ring
#print axioms pivot89Four_binding
end QuantitativeArithmeticSmallLevelTwentySixSourceBridge
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySixSourcePivot89RawBindingV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixSourceBridge
theorem pivot89Raw_binding (x y z w a b u : ℂ) :
    QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.p6 x y z w a b u=SmallLevelTwentySixPariSourcePolynomial89.polynomial x y z w a b u := by
  calc
    QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.p6 x y z w a b u=(((((((((((((((((QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_17 y z w a b u)*x+(QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_16 y z w a b u))*x+(QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_15 y z w a b u))*x+(QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_14 y z w a b u))*x+(QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_13 y z w a b u))*x+(QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_12 y z w a b u))*x+(QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_11 y z w a b u))*x+(QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_10 y z w a b u))*x+(QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_9 y z w a b u))*x+(QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_8 y z w a b u))*x+(QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_7 y z w a b u))*x+(QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_6 y z w a b u))*x+(QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_5 y z w a b u))*x+(QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_4 y z w a b u))*x+(QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_3 y z w a b u))*x+(QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_2 y z w a b u))*x+(QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_1 y z w a b u))*x := by
      simp only [QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.p6,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.coefficients6,
        SmallLevelPolynomialCoefficientCertificate.evaluate,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_0]
      ring
    _=SmallLevelTwentySixPariSourcePolynomial89.polynomial x y z w a b u := by
      simp only [SmallLevelTwentySixPariSourcePolynomial89.polynomial,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_0,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_1,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_10,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_11,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_12,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_13,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_14,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_15,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_16,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_17,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_2,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_3,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_4,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_5,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_6,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_7,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_8,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c6_9]
#print axioms pivot89Raw_binding
end QuantitativeArithmeticSmallLevelTwentySixSourceBridge
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySixSourcePivot89SixBindingV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixSourceBridge
theorem pivot89Six_binding (x y z w a b u : ℂ) :
    QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.p2 x y z w a b u=SmallLevelTwentySixPariSourcePivots.source6 x y z w a b u := by
  simp only [QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.p2,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.coefficients2,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c2_0,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c2_1,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c2_2,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c2_3,QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.c2_4,SmallLevelTwentySixPariSourcePivots.source6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  first | rfl | ac_rfl | ring
#print axioms pivot89Six_binding
end QuantitativeArithmeticSmallLevelTwentySixSourceBridge
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySixSourceResultant89CoefficientsV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixSourceBridge
theorem resultant89_coefficient_0 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_0 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_0 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_0,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_0]
theorem resultant89_coefficient_1 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_1 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_1 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_1,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_1]
theorem resultant89_coefficient_2 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_2 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_2 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_2,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_2]
theorem resultant89_coefficient_3 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_3 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_3 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_3,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_3]
theorem resultant89_coefficient_4 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_4 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_4 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_4,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_4]
theorem resultant89_coefficient_5 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_5 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_5 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_5,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_5]
theorem resultant89_coefficient_6 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_6 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_6 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_6,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_6]
theorem resultant89_coefficient_7 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_7 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_7 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_7,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_7]
theorem resultant89_coefficient_8 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_8 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_8 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_8,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_8]
theorem resultant89_coefficient_9 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_9 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_9 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_9,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_9]
theorem resultant89_coefficient_10 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_10 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_10 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_10,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_10]
theorem resultant89_coefficient_11 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_11 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_11 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_11,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_11]
theorem resultant89_coefficient_12 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_12 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_12 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_12,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_12]
theorem resultant89_coefficient_13 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_13 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_13 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_13,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_13]
theorem resultant89_coefficient_14 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_14 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_14 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_14,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_14]
theorem resultant89_coefficient_15 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_15 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_15 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_15,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_15]
theorem resultant89_coefficient_16 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_16 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_16 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_16,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_16]
theorem resultant89_coefficient_17 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_17 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_17 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_17,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_17]
theorem resultant89_coefficient_18 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_18 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_18 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_18,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_18]
theorem resultant89_coefficient_19 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_19 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_19 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_19,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_19]
theorem resultant89_coefficient_20 (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.c2_20 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_20 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.c2_20,QuantitativeArithmeticSmallLevelTwentySixSourceW89.c4_20]
theorem resultant89_coefficients (y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.coefficients2 y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.coefficients4 y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.coefficients2,QuantitativeArithmeticSmallLevelTwentySixSourceW89.coefficients4,resultant89_coefficient_0,resultant89_coefficient_1,resultant89_coefficient_2,resultant89_coefficient_3,resultant89_coefficient_4,resultant89_coefficient_5,resultant89_coefficient_6,resultant89_coefficient_7,resultant89_coefficient_8,resultant89_coefficient_9,resultant89_coefficient_10,resultant89_coefficient_11,resultant89_coefficient_12,resultant89_coefficient_13,resultant89_coefficient_14,resultant89_coefficient_15,resultant89_coefficient_16,resultant89_coefficient_17,resultant89_coefficient_18,resultant89_coefficient_19,resultant89_coefficient_20]
#print axioms resultant89_coefficients
end QuantitativeArithmeticSmallLevelTwentySixSourceBridge
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySixSourceResultant89SourceBindingV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixSourceBridge
theorem resultant89Source_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.p0 x y z w a b u=SmallLevelTwentySixPariIdentity004.p0 x y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant89.p0,SmallLevelTwentySixSourceResultant89.coefficients0,SmallLevelTwentySixSourceResultant89.c0_0,SmallLevelTwentySixSourceResultant89.c0_1,SmallLevelTwentySixSourceResultant89.c0_2,SmallLevelTwentySixSourceResultant89.c0_3,SmallLevelTwentySixPariIdentity004.p0,SmallLevelPolynomialCoefficientCertificate.evaluate]
  first | rfl | ac_rfl | ring
#print axioms resultant89Source_binding
end QuantitativeArithmeticSmallLevelTwentySixSourceBridge
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySixSourceResultant89WBindingV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixSourceBridge
theorem resultant89W_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.p2 x y z w a b u=QuantitativeArithmeticSmallLevelTwentySixSourceW89.p4 x y z w a b u := by
  exact congrArg (SmallLevelPolynomialCoefficientCertificate.evaluate x)
    (resultant89_coefficients y z w a b u)
#print axioms resultant89W_binding
end QuantitativeArithmeticSmallLevelTwentySixSourceBridge
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySixSourceW89LeftBindingV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixSourceBridge
theorem w89Left_binding (x y z w a b u : ℂ) :
    x*(QuantitativeArithmeticSmallLevelTwentySixSourceW89.p1 x y z w a b u)=QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.p4 x y z w a b u := by
  have hc : QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.coefficients4 y z w a b u=
      0::QuantitativeArithmeticSmallLevelTwentySixSourceW89.coefficients1 y z w a b u := by rfl
  rw [QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.p4,hc,QuantitativeArithmeticSmallLevelTwentySixSourceW89.p1,SmallLevelPolynomialCoefficientCertificate.evaluate,zero_add]
#print axioms w89Left_binding
end QuantitativeArithmeticSmallLevelTwentySixSourceBridge
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySixSourceW89RightBindingV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixSourceBridge
theorem w89Right_binding (x y z w a b u : ℂ) :
    x*(QuantitativeArithmeticSmallLevelTwentySixSourceW89.p3 x y z w a b u)=SmallLevelTwentySixPariSourcePivot8.p4 x y z w a b u := by
  have hc : SmallLevelTwentySixPariSourcePivot8.coefficients4 y z w a b u=
      0::QuantitativeArithmeticSmallLevelTwentySixSourceW89.coefficients3 y z w a b u := by rfl
  rw [SmallLevelTwentySixPariSourcePivot8.p4,hc,QuantitativeArithmeticSmallLevelTwentySixSourceW89.p3,SmallLevelPolynomialCoefficientCertificate.evaluate,zero_add]
#print axioms w89Right_binding
end QuantitativeArithmeticSmallLevelTwentySixSourceBridge
end
end

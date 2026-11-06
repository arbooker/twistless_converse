module
public import SmallLevelTwentySixMMPPariTraceThirtyThreeV4
public import SmallLevelTwentySixMMPPariTraceIndexFamilyDataV4
public meta import SmallLevelPolynomialCertificateCommandsV4
public import SmallLevelPolynomialCoefficientCertificateTheoryV4
public import SmallLevelPolynomialZeroPrefixV1
set_option Elab.async false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
section
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace040
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_length (y z w a b u : ℂ) : (certificate y z w a b u).length=41 := by
  norm_num [certificate,add,multiply,scale,coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6]

end SmallLevelTwentySixMMPPariTrace040
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace040
open SmallLevelPolynomialCoefficientCertificate

certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 0 through 40 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, c1_6, c1_7, c1_8, c1_9, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, c2_11, c2_12, c2_13, c2_14, c2_15, c2_16, c2_17, c2_18, c2_19, c2_20, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, c3_20, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, coefficients4, c5_0, c5_1, c5_2, c5_3, c5_4, c5_5, c5_6, c5_7, c5_8, c5_9, c5_10, c5_11, c5_12, c5_13, c5_14, c5_15, c5_16, c5_17, c5_18, c5_19, c5_20, c5_21, coefficients5, c6_0, c6_1, c6_2, c6_3, c6_4, c6_5, c6_6, c6_7, c6_8, c6_9, c6_10, c6_11, c6_12, c6_13, c6_14, c6_15, c6_16, c6_17, c6_18, c6_19, coefficients6, certificate]

end SmallLevelTwentySixMMPPariTrace040
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace040
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_zero (y z w a b u : ℂ) : ∀ v∈certificate y z w a b u,v=0 := by
  apply zero_of_getElem? _ 41 (certificate_length y z w a b u)
  intro i
  fin_cases i
  · exact coefficient_0 y z w a b u
  · exact coefficient_1 y z w a b u
  · exact coefficient_2 y z w a b u
  · exact coefficient_3 y z w a b u
  · exact coefficient_4 y z w a b u
  · exact coefficient_5 y z w a b u
  · exact coefficient_6 y z w a b u
  · exact coefficient_7 y z w a b u
  · exact coefficient_8 y z w a b u
  · exact coefficient_9 y z w a b u
  · exact coefficient_10 y z w a b u
  · exact coefficient_11 y z w a b u
  · exact coefficient_12 y z w a b u
  · exact coefficient_13 y z w a b u
  · exact coefficient_14 y z w a b u
  · exact coefficient_15 y z w a b u
  · exact coefficient_16 y z w a b u
  · exact coefficient_17 y z w a b u
  · exact coefficient_18 y z w a b u
  · exact coefficient_19 y z w a b u
  · exact coefficient_20 y z w a b u
  · exact coefficient_21 y z w a b u
  · exact coefficient_22 y z w a b u
  · exact coefficient_23 y z w a b u
  · exact coefficient_24 y z w a b u
  · exact coefficient_25 y z w a b u
  · exact coefficient_26 y z w a b u
  · exact coefficient_27 y z w a b u
  · exact coefficient_28 y z w a b u
  · exact coefficient_29 y z w a b u
  · exact coefficient_30 y z w a b u
  · exact coefficient_31 y z w a b u
  · exact coefficient_32 y z w a b u
  · exact coefficient_33 y z w a b u
  · exact coefficient_34 y z w a b u
  · exact coefficient_35 y z w a b u
  · exact coefficient_36 y z w a b u
  · exact coefficient_37 y z w a b u
  · exact coefficient_38 y z w a b u
  · exact coefficient_39 y z w a b u
  · exact coefficient_40 y z w a b u
compact_certificate_declaration theorem identity (x y z w a b u : ℂ) :
    p0 x y z w a b u*p1 x y z w a b u+p2 x y z w a b u*p3 x y z w a b u=
      p4 x y z w a b u+p5 x y z w a b u*p6 x y z w a b u := by
  unfold p0 p1 p2 p3 p4 p5 p6
  exact of_zero_coefficients x _ _ _ _ _ _ _ (certificate_zero y z w a b u)
#print axioms identity

end SmallLevelTwentySixMMPPariTrace040
end
end

section
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace047
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_length (y z w a b u : ℂ) : (certificate y z w a b u).length=33 := by
  norm_num [certificate,add,multiply,scale,coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6]

end SmallLevelTwentySixMMPPariTrace047
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace047
open SmallLevelPolynomialCoefficientCertificate

certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 0 through 32 unfolding [c0_0, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, c1_6, c1_7, c1_8, c1_9, c1_10, c1_11, c1_12, c1_13, c1_14, c1_15, c1_16, c1_17, c1_18, c1_19, c1_20, c1_21, c1_22, c1_23, c1_24, c1_25, c1_26, c1_27, c1_28, c1_29, c1_30, c1_31, c1_32, coefficients1, coefficients2, coefficients3, c4_0, c4_1, coefficients4, c5_0, c5_1, c5_2, coefficients5, c6_0, c6_1, c6_2, c6_3, c6_4, c6_5, c6_6, c6_7, c6_8, c6_9, c6_10, c6_11, c6_12, c6_13, c6_14, c6_15, c6_16, c6_17, c6_18, c6_19, c6_20, c6_21, c6_22, c6_23, c6_24, c6_25, c6_26, c6_27, c6_28, c6_29, c6_30, coefficients6, certificate]

end SmallLevelTwentySixMMPPariTrace047
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace047
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_zero (y z w a b u : ℂ) : ∀ v∈certificate y z w a b u,v=0 := by
  apply zero_of_getElem? _ 33 (certificate_length y z w a b u)
  intro i
  fin_cases i
  · exact coefficient_0 y z w a b u
  · exact coefficient_1 y z w a b u
  · exact coefficient_2 y z w a b u
  · exact coefficient_3 y z w a b u
  · exact coefficient_4 y z w a b u
  · exact coefficient_5 y z w a b u
  · exact coefficient_6 y z w a b u
  · exact coefficient_7 y z w a b u
  · exact coefficient_8 y z w a b u
  · exact coefficient_9 y z w a b u
  · exact coefficient_10 y z w a b u
  · exact coefficient_11 y z w a b u
  · exact coefficient_12 y z w a b u
  · exact coefficient_13 y z w a b u
  · exact coefficient_14 y z w a b u
  · exact coefficient_15 y z w a b u
  · exact coefficient_16 y z w a b u
  · exact coefficient_17 y z w a b u
  · exact coefficient_18 y z w a b u
  · exact coefficient_19 y z w a b u
  · exact coefficient_20 y z w a b u
  · exact coefficient_21 y z w a b u
  · exact coefficient_22 y z w a b u
  · exact coefficient_23 y z w a b u
  · exact coefficient_24 y z w a b u
  · exact coefficient_25 y z w a b u
  · exact coefficient_26 y z w a b u
  · exact coefficient_27 y z w a b u
  · exact coefficient_28 y z w a b u
  · exact coefficient_29 y z w a b u
  · exact coefficient_30 y z w a b u
  · exact coefficient_31 y z w a b u
  · exact coefficient_32 y z w a b u
compact_certificate_declaration theorem identity (x y z w a b u : ℂ) :
    p0 x y z w a b u*p1 x y z w a b u+p2 x y z w a b u*p3 x y z w a b u=
      p4 x y z w a b u+p5 x y z w a b u*p6 x y z w a b u := by
  unfold p0 p1 p2 p3 p4 p5 p6
  exact of_zero_coefficients x _ _ _ _ _ _ _ (certificate_zero y z w a b u)
#print axioms identity

end SmallLevelTwentySixMMPPariTrace047
end
end

section
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace050
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_length (y z w a b u : ℂ) : (certificate y z w a b u).length=33 := by
  norm_num [certificate,add,multiply,scale,coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6]

end SmallLevelTwentySixMMPPariTrace050
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace050
open SmallLevelPolynomialCoefficientCertificate

certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 0 through 32 unfolding [c0_0, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, c1_6, c1_7, c1_8, c1_9, c1_10, c1_11, c1_12, c1_13, c1_14, c1_15, c1_16, c1_17, c1_18, c1_19, c1_20, c1_21, c1_22, c1_23, c1_24, c1_25, c1_26, c1_27, c1_28, c1_29, c1_30, c1_31, c1_32, coefficients1, coefficients2, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, coefficients4, c5_0, c5_1, c5_2, c5_3, c5_4, c5_5, c5_6, c5_7, c5_8, c5_9, c5_10, c5_11, c5_12, c5_13, c5_14, c5_15, c5_16, c5_17, c5_18, c5_19, c5_20, c5_21, coefficients5, c6_0, c6_1, c6_2, c6_3, c6_4, c6_5, c6_6, c6_7, c6_8, c6_9, c6_10, c6_11, coefficients6, certificate]

end SmallLevelTwentySixMMPPariTrace050
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace050
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_zero (y z w a b u : ℂ) : ∀ v∈certificate y z w a b u,v=0 := by
  apply zero_of_getElem? _ 33 (certificate_length y z w a b u)
  intro i
  fin_cases i
  · exact coefficient_0 y z w a b u
  · exact coefficient_1 y z w a b u
  · exact coefficient_2 y z w a b u
  · exact coefficient_3 y z w a b u
  · exact coefficient_4 y z w a b u
  · exact coefficient_5 y z w a b u
  · exact coefficient_6 y z w a b u
  · exact coefficient_7 y z w a b u
  · exact coefficient_8 y z w a b u
  · exact coefficient_9 y z w a b u
  · exact coefficient_10 y z w a b u
  · exact coefficient_11 y z w a b u
  · exact coefficient_12 y z w a b u
  · exact coefficient_13 y z w a b u
  · exact coefficient_14 y z w a b u
  · exact coefficient_15 y z w a b u
  · exact coefficient_16 y z w a b u
  · exact coefficient_17 y z w a b u
  · exact coefficient_18 y z w a b u
  · exact coefficient_19 y z w a b u
  · exact coefficient_20 y z w a b u
  · exact coefficient_21 y z w a b u
  · exact coefficient_22 y z w a b u
  · exact coefficient_23 y z w a b u
  · exact coefficient_24 y z w a b u
  · exact coefficient_25 y z w a b u
  · exact coefficient_26 y z w a b u
  · exact coefficient_27 y z w a b u
  · exact coefficient_28 y z w a b u
  · exact coefficient_29 y z w a b u
  · exact coefficient_30 y z w a b u
  · exact coefficient_31 y z w a b u
  · exact coefficient_32 y z w a b u
compact_certificate_declaration theorem identity (x y z w a b u : ℂ) :
    p0 x y z w a b u*p1 x y z w a b u+p2 x y z w a b u*p3 x y z w a b u=
      p4 x y z w a b u+p5 x y z w a b u*p6 x y z w a b u := by
  unfold p0 p1 p2 p3 p4 p5 p6
  exact of_zero_coefficients x _ _ _ _ _ _ _ (certificate_zero y z w a b u)
#print axioms identity

end SmallLevelTwentySixMMPPariTrace050
end
end

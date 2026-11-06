module
public import SmallLevelTwentySixMMPPariTraceTwentySixThirdTablesV4
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

namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_24 (y z w b u : ℂ) : (innerCertificate24 y z w b u).length=8 := by
  norm_num [innerCertificate24,add,multiply,scale,inner0_21,inner0_22,inner0_23,inner0_24,inner1_0,inner1_1,inner1_2,inner1_3,inner2_10,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_14,inner3_15,inner3_16,inner3_17,inner3_18,inner3_19,inner4_24]
compact_certificate_declaration theorem inner_eval_24 (y z w a b u : ℂ) :
    evaluate a (innerCertificate24 y z w b u)=(((((c0_21 y z w a b u)*(c1_3 y z w a b u))+(((c0_22 y z w a b u)*(c1_2 y z w a b u))+(((c0_23 y z w a b u)*(c1_1 y z w a b u))+(((c0_24 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_5 y z w a b u)*(c3_19 y z w a b u))+(((c2_6 y z w a b u)*(c3_18 y z w a b u))+(((c2_7 y z w a b u)*(c3_17 y z w a b u))+(((c2_8 y z w a b u)*(c3_16 y z w a b u))+(((c2_9 y z w a b u)*(c3_15 y z w a b u))+((c2_10 y z w a b u)*(c3_14 y z w a b u))))))))+((-1)*(c4_24 y z w a b u))) := by
  simp only [innerCertificate24,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_21,c0_22,c0_23,c0_24,c1_0,c1_1,c1_2,c1_3,c2_10,c2_5,c2_6,c2_7,c2_8,c2_9,c3_14,c3_15,c3_16,c3_17,c3_18,c3_19,c4_24]
#print axioms inner_eval_24

end SmallLevelTwentySixMMPPariTrace026
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_24_0 (y z w b u : ℂ) :
    (innerCertificate24 y z w b u)[0]?=some 0 := by
  change some (((((((d0_21_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_22_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_23_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_24_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_5_0 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_6_0 y z w b u)*(d3_18_0 y z w b u))+0)+((((d2_7_0 y z w b u)*(d3_17_0 y z w b u))+0)+((((d2_8_0 y z w b u)*(d3_16_0 y z w b u))+0)+((((d2_9_0 y z w b u)*(d3_15_0 y z w b u))+0)+(((d2_10_0 y z w b u)*(d3_14_0 y z w b u))+0)))))))+(((-1)*(d4_24_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_21_0,d0_22_0,d0_23_0,d0_24_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_10_0,d2_5_0,d2_6_0,d2_7_0,d2_8_0,d2_9_0,d3_14_0,d3_15_0,d3_16_0,d3_17_0,d3_18_0,d3_19_0,d4_24_0]
  ring
#print axioms coefficient_24_0
compact_certificate_declaration theorem coefficient_24_1 (y z w b u : ℂ) :
    (innerCertificate24 y z w b u)[1]?=some 0 := by
  change some (((((((d0_21_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_22_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_23_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_23_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_24_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_24_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_5_1 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_6_0 y z w b u)*(d3_18_1 y z w b u))+(((d2_6_1 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_7_0 y z w b u)*(d3_17_1 y z w b u))+(((d2_7_1 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_8_0 y z w b u)*(d3_16_1 y z w b u))+(((d2_8_1 y z w b u)*(d3_16_0 y z w b u))+0))+((((d2_9_0 y z w b u)*(d3_15_1 y z w b u))+(((d2_9_1 y z w b u)*(d3_15_0 y z w b u))+0))+((d2_10_0 y z w b u)*(d3_14_1 y z w b u))))))))+((-1)*(d4_24_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_21_1,d0_22_1,d0_23_0,d0_23_1,d0_24_0,d0_24_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_5_1,d2_6_0,d2_6_1,d2_7_0,d2_7_1,d2_8_0,d2_8_1,d2_9_0,d2_9_1,d3_14_1,d3_15_0,d3_15_1,d3_16_0,d3_16_1,d3_17_0,d3_17_1,d3_18_0,d3_18_1,d3_19_0,d4_24_1]
  ring
#print axioms coefficient_24_1
compact_certificate_declaration theorem coefficient_24_2 (y z w b u : ℂ) :
    (innerCertificate24 y z w b u)[2]?=some 0 := by
  change some (((((((d0_21_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_22_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_23_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_23_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_24_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_24_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_5_2 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_6_1 y z w b u)*(d3_18_1 y z w b u))+(((d2_6_2 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_7_0 y z w b u)*(d3_17_2 y z w b u))+(((d2_7_1 y z w b u)*(d3_17_1 y z w b u))+(((d2_7_2 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_8_0 y z w b u)*(d3_16_2 y z w b u))+(((d2_8_1 y z w b u)*(d3_16_1 y z w b u))+(((d2_8_2 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_9_0 y z w b u)*(d3_15_2 y z w b u))+((d2_9_1 y z w b u)*(d3_15_1 y z w b u)))+((d2_10_0 y z w b u)*(d3_14_2 y z w b u))))))))+((-1)*(d4_24_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_21_2,d0_22_2,d0_23_1,d0_23_2,d0_24_1,d0_24_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_5_2,d2_6_1,d2_6_2,d2_7_0,d2_7_1,d2_7_2,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_14_2,d3_15_1,d3_15_2,d3_16_0,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_24_2]
  ring
#print axioms coefficient_24_2

compact_certificate_declaration theorem coefficient_24_3 (y z w b u : ℂ) :
    (innerCertificate24 y z w b u)[3]?=some 0 := by
  change some (((((((d0_21_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_22_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_23_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_23_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_24_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_24_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_5_3 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_6_2 y z w b u)*(d3_18_1 y z w b u))+(((d2_6_3 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_7_1 y z w b u)*(d3_17_2 y z w b u))+(((d2_7_2 y z w b u)*(d3_17_1 y z w b u))+(((d2_7_3 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_8_0 y z w b u)*(d3_16_3 y z w b u))+(((d2_8_1 y z w b u)*(d3_16_2 y z w b u))+((d2_8_2 y z w b u)*(d3_16_1 y z w b u))))+((((d2_9_0 y z w b u)*(d3_15_3 y z w b u))+((d2_9_1 y z w b u)*(d3_15_2 y z w b u)))+((d2_10_0 y z w b u)*(d3_14_3 y z w b u))))))))+((-1)*(d4_24_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_21_3,d0_22_3,d0_23_2,d0_23_3,d0_24_2,d0_24_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_5_3,d2_6_2,d2_6_3,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_14_3,d3_15_2,d3_15_3,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_24_3]
  ring
#print axioms coefficient_24_3
compact_certificate_declaration theorem coefficient_24_4 (y z w b u : ℂ) :
    (innerCertificate24 y z w b u)[4]?=some 0 := by
  change some (((((((d0_21_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_22_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_23_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_23_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_24_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_24_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_5_4 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_6_3 y z w b u)*(d3_18_1 y z w b u))+(((d2_6_4 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_7_2 y z w b u)*(d3_17_2 y z w b u))+((d2_7_3 y z w b u)*(d3_17_1 y z w b u)))+((((d2_8_1 y z w b u)*(d3_16_3 y z w b u))+((d2_8_2 y z w b u)*(d3_16_2 y z w b u)))+((((d2_9_0 y z w b u)*(d3_15_4 y z w b u))+((d2_9_1 y z w b u)*(d3_15_3 y z w b u)))+((d2_10_0 y z w b u)*(d3_14_4 y z w b u))))))))+((-1)*(d4_24_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_21_4,d0_22_4,d0_23_3,d0_23_4,d0_24_3,d0_24_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_5_4,d2_6_3,d2_6_4,d2_7_2,d2_7_3,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_14_4,d3_15_3,d3_15_4,d3_16_2,d3_16_3,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_24_4]
  ring
#print axioms coefficient_24_4
compact_certificate_declaration theorem coefficient_24_5 (y z w b u : ℂ) :
    (innerCertificate24 y z w b u)[5]?=some 0 := by
  change some (((((((d0_21_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_22_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_23_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_23_5 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_24_4 y z w b u)*(d1_0_1 y z w b u)))))+((((d2_5_5 y z w b u)*(d3_19_0 y z w b u))+0)+(((d2_6_4 y z w b u)*(d3_18_1 y z w b u))+(((d2_7_3 y z w b u)*(d3_17_2 y z w b u))+(((d2_8_2 y z w b u)*(d3_16_3 y z w b u))+((d2_9_1 y z w b u)*(d3_15_4 y z w b u)))))))+((-1)*(d4_24_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_21_5,d0_22_5,d0_23_4,d0_23_5,d0_24_4,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_5_5,d2_6_4,d2_7_3,d2_8_2,d2_9_1,d3_15_4,d3_16_3,d3_17_2,d3_18_1,d3_19_0,d4_24_5]
  ring
#print axioms coefficient_24_5

compact_certificate_declaration theorem coefficient_24_6 (y z w b u : ℂ) :
    (innerCertificate24 y z w b u)[6]?=some 0 := by
  change some ((((((d0_21_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_22_6 y z w b u)*(d1_2_0 y z w b u))+0)+((d0_23_5 y z w b u)*(d1_1_1 y z w b u))))+((-1)*(d4_24_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_21_6,d0_22_6,d0_23_5,d1_1_1,d1_2_0,d1_3_0,d4_24_6]
  ring
#print axioms coefficient_24_6
compact_certificate_declaration theorem coefficient_24_7 (y z w b u : ℂ) :
    (innerCertificate24 y z w b u)[7]?=some 0 := by
  change some (((((d0_21_7 y z w b u)*(d1_3_0 y z w b u))+0)+((-1)*(d4_24_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_21_7,d1_3_0,d4_24_7]
  ring
#print axioms coefficient_24_7

end SmallLevelTwentySixMMPPariTrace026
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_25 (y z w b u : ℂ) : (innerCertificate25 y z w b u).length=7 := by
  norm_num [innerCertificate25,add,multiply,scale,inner0_22,inner0_23,inner0_24,inner0_25,inner1_0,inner1_1,inner1_2,inner1_3,inner2_10,inner2_6,inner2_7,inner2_8,inner2_9,inner3_15,inner3_16,inner3_17,inner3_18,inner3_19,inner4_25]
compact_certificate_declaration theorem inner_eval_25 (y z w a b u : ℂ) :
    evaluate a (innerCertificate25 y z w b u)=(((((c0_22 y z w a b u)*(c1_3 y z w a b u))+(((c0_23 y z w a b u)*(c1_2 y z w a b u))+(((c0_24 y z w a b u)*(c1_1 y z w a b u))+(((c0_25 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_6 y z w a b u)*(c3_19 y z w a b u))+(((c2_7 y z w a b u)*(c3_18 y z w a b u))+(((c2_8 y z w a b u)*(c3_17 y z w a b u))+(((c2_9 y z w a b u)*(c3_16 y z w a b u))+((c2_10 y z w a b u)*(c3_15 y z w a b u)))))))+((-1)*(c4_25 y z w a b u))) := by
  simp only [innerCertificate25,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_22,c0_23,c0_24,c0_25,c1_0,c1_1,c1_2,c1_3,c2_10,c2_6,c2_7,c2_8,c2_9,c3_15,c3_16,c3_17,c3_18,c3_19,c4_25]
#print axioms inner_eval_25

end SmallLevelTwentySixMMPPariTrace026
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_25_0 (y z w b u : ℂ) :
    (innerCertificate25 y z w b u)[0]?=some 0 := by
  change some (((((((d0_22_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_23_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_24_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_25_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_6_0 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_7_0 y z w b u)*(d3_18_0 y z w b u))+0)+((((d2_8_0 y z w b u)*(d3_17_0 y z w b u))+0)+((((d2_9_0 y z w b u)*(d3_16_0 y z w b u))+0)+(((d2_10_0 y z w b u)*(d3_15_0 y z w b u))+0))))))+(((-1)*(d4_25_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_22_0,d0_23_0,d0_24_0,d0_25_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_10_0,d2_6_0,d2_7_0,d2_8_0,d2_9_0,d3_15_0,d3_16_0,d3_17_0,d3_18_0,d3_19_0,d4_25_0]
  ring
#print axioms coefficient_25_0
compact_certificate_declaration theorem coefficient_25_1 (y z w b u : ℂ) :
    (innerCertificate25 y z w b u)[1]?=some 0 := by
  change some (((((((d0_22_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_23_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_24_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_24_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_25_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_25_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_6_1 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_7_0 y z w b u)*(d3_18_1 y z w b u))+(((d2_7_1 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_8_0 y z w b u)*(d3_17_1 y z w b u))+(((d2_8_1 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_9_0 y z w b u)*(d3_16_1 y z w b u))+(((d2_9_1 y z w b u)*(d3_16_0 y z w b u))+0))+((d2_10_0 y z w b u)*(d3_15_1 y z w b u)))))))+((-1)*(d4_25_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_22_1,d0_23_1,d0_24_0,d0_24_1,d0_25_0,d0_25_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_6_1,d2_7_0,d2_7_1,d2_8_0,d2_8_1,d2_9_0,d2_9_1,d3_15_1,d3_16_0,d3_16_1,d3_17_0,d3_17_1,d3_18_0,d3_18_1,d3_19_0,d4_25_1]
  ring
#print axioms coefficient_25_1
compact_certificate_declaration theorem coefficient_25_2 (y z w b u : ℂ) :
    (innerCertificate25 y z w b u)[2]?=some 0 := by
  change some (((((((d0_22_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_23_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_24_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_24_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_25_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_25_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_6_2 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_7_1 y z w b u)*(d3_18_1 y z w b u))+(((d2_7_2 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_8_0 y z w b u)*(d3_17_2 y z w b u))+(((d2_8_1 y z w b u)*(d3_17_1 y z w b u))+(((d2_8_2 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_9_0 y z w b u)*(d3_16_2 y z w b u))+((d2_9_1 y z w b u)*(d3_16_1 y z w b u)))+((d2_10_0 y z w b u)*(d3_15_2 y z w b u)))))))+((-1)*(d4_25_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_22_2,d0_23_2,d0_24_1,d0_24_2,d0_25_1,d0_25_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_6_2,d2_7_1,d2_7_2,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_15_2,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_25_2]
  ring
#print axioms coefficient_25_2

compact_certificate_declaration theorem coefficient_25_3 (y z w b u : ℂ) :
    (innerCertificate25 y z w b u)[3]?=some 0 := by
  change some (((((((d0_22_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_23_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_24_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_24_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_25_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_25_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_6_3 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_7_2 y z w b u)*(d3_18_1 y z w b u))+(((d2_7_3 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_8_1 y z w b u)*(d3_17_2 y z w b u))+((d2_8_2 y z w b u)*(d3_17_1 y z w b u)))+((((d2_9_0 y z w b u)*(d3_16_3 y z w b u))+((d2_9_1 y z w b u)*(d3_16_2 y z w b u)))+((d2_10_0 y z w b u)*(d3_15_3 y z w b u)))))))+((-1)*(d4_25_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_22_3,d0_23_3,d0_24_2,d0_24_3,d0_25_2,d0_25_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_6_3,d2_7_2,d2_7_3,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_15_3,d3_16_2,d3_16_3,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_25_3]
  ring
#print axioms coefficient_25_3
compact_certificate_declaration theorem coefficient_25_4 (y z w b u : ℂ) :
    (innerCertificate25 y z w b u)[4]?=some 0 := by
  change some (((((((d0_22_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_23_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_24_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_24_4 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_25_3 y z w b u)*(d1_0_1 y z w b u)))))+((((d2_6_4 y z w b u)*(d3_19_0 y z w b u))+0)+(((d2_7_3 y z w b u)*(d3_18_1 y z w b u))+(((d2_8_2 y z w b u)*(d3_17_2 y z w b u))+(((d2_9_1 y z w b u)*(d3_16_3 y z w b u))+((d2_10_0 y z w b u)*(d3_15_4 y z w b u)))))))+((-1)*(d4_25_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_22_4,d0_23_4,d0_24_3,d0_24_4,d0_25_3,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_6_4,d2_7_3,d2_8_2,d2_9_1,d3_15_4,d3_16_3,d3_17_2,d3_18_1,d3_19_0,d4_25_4]
  ring
#print axioms coefficient_25_4
compact_certificate_declaration theorem coefficient_25_5 (y z w b u : ℂ) :
    (innerCertificate25 y z w b u)[5]?=some 0 := by
  change some ((((((d0_22_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_23_5 y z w b u)*(d1_2_0 y z w b u))+0)+((d0_24_4 y z w b u)*(d1_1_1 y z w b u))))+((-1)*(d4_25_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_22_5,d0_23_5,d0_24_4,d1_1_1,d1_2_0,d1_3_0,d4_25_5]
  ring
#print axioms coefficient_25_5

compact_certificate_declaration theorem coefficient_25_6 (y z w b u : ℂ) :
    (innerCertificate25 y z w b u)[6]?=some 0 := by
  change some (((((d0_22_6 y z w b u)*(d1_3_0 y z w b u))+0)+((-1)*(d4_25_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_22_6,d1_3_0,d4_25_6]
  ring
#print axioms coefficient_25_6

end SmallLevelTwentySixMMPPariTrace026
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_26 (y z w b u : ℂ) : (innerCertificate26 y z w b u).length=6 := by
  norm_num [innerCertificate26,add,multiply,scale,inner0_23,inner0_24,inner0_25,inner0_26,inner1_0,inner1_1,inner1_2,inner1_3,inner2_10,inner2_7,inner2_8,inner2_9,inner3_16,inner3_17,inner3_18,inner3_19,inner4_26]
compact_certificate_declaration theorem inner_eval_26 (y z w a b u : ℂ) :
    evaluate a (innerCertificate26 y z w b u)=(((((c0_23 y z w a b u)*(c1_3 y z w a b u))+(((c0_24 y z w a b u)*(c1_2 y z w a b u))+(((c0_25 y z w a b u)*(c1_1 y z w a b u))+(((c0_26 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_7 y z w a b u)*(c3_19 y z w a b u))+(((c2_8 y z w a b u)*(c3_18 y z w a b u))+(((c2_9 y z w a b u)*(c3_17 y z w a b u))+((c2_10 y z w a b u)*(c3_16 y z w a b u))))))+((-1)*(c4_26 y z w a b u))) := by
  simp only [innerCertificate26,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_23,c0_24,c0_25,c0_26,c1_0,c1_1,c1_2,c1_3,c2_10,c2_7,c2_8,c2_9,c3_16,c3_17,c3_18,c3_19,c4_26]
#print axioms inner_eval_26

end SmallLevelTwentySixMMPPariTrace026
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_26_0 (y z w b u : ℂ) :
    (innerCertificate26 y z w b u)[0]?=some 0 := by
  change some (((((((d0_23_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_24_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_25_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_26_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_7_0 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_8_0 y z w b u)*(d3_18_0 y z w b u))+0)+((((d2_9_0 y z w b u)*(d3_17_0 y z w b u))+0)+(((d2_10_0 y z w b u)*(d3_16_0 y z w b u))+0)))))+(((-1)*(d4_26_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_23_0,d0_24_0,d0_25_0,d0_26_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_10_0,d2_7_0,d2_8_0,d2_9_0,d3_16_0,d3_17_0,d3_18_0,d3_19_0,d4_26_0]
  ring
#print axioms coefficient_26_0
compact_certificate_declaration theorem coefficient_26_1 (y z w b u : ℂ) :
    (innerCertificate26 y z w b u)[1]?=some 0 := by
  change some (((((((d0_23_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_24_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_25_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_25_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_26_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_26_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_7_1 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_8_0 y z w b u)*(d3_18_1 y z w b u))+(((d2_8_1 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_9_0 y z w b u)*(d3_17_1 y z w b u))+(((d2_9_1 y z w b u)*(d3_17_0 y z w b u))+0))+((d2_10_0 y z w b u)*(d3_16_1 y z w b u))))))+((-1)*(d4_26_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_23_1,d0_24_1,d0_25_0,d0_25_1,d0_26_0,d0_26_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_7_1,d2_8_0,d2_8_1,d2_9_0,d2_9_1,d3_16_1,d3_17_0,d3_17_1,d3_18_0,d3_18_1,d3_19_0,d4_26_1]
  ring
#print axioms coefficient_26_1
compact_certificate_declaration theorem coefficient_26_2 (y z w b u : ℂ) :
    (innerCertificate26 y z w b u)[2]?=some 0 := by
  change some (((((((d0_23_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_24_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_25_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_25_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_26_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_26_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_7_2 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_8_1 y z w b u)*(d3_18_1 y z w b u))+(((d2_8_2 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_9_0 y z w b u)*(d3_17_2 y z w b u))+((d2_9_1 y z w b u)*(d3_17_1 y z w b u)))+((d2_10_0 y z w b u)*(d3_16_2 y z w b u))))))+((-1)*(d4_26_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_23_2,d0_24_2,d0_25_1,d0_25_2,d0_26_1,d0_26_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_7_2,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_16_2,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_26_2]
  ring
#print axioms coefficient_26_2

compact_certificate_declaration theorem coefficient_26_3 (y z w b u : ℂ) :
    (innerCertificate26 y z w b u)[3]?=some 0 := by
  change some (((((((d0_23_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_24_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_25_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_25_3 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_26_2 y z w b u)*(d1_0_1 y z w b u)))))+((((d2_7_3 y z w b u)*(d3_19_0 y z w b u))+0)+(((d2_8_2 y z w b u)*(d3_18_1 y z w b u))+(((d2_9_1 y z w b u)*(d3_17_2 y z w b u))+((d2_10_0 y z w b u)*(d3_16_3 y z w b u))))))+((-1)*(d4_26_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_23_3,d0_24_3,d0_25_2,d0_25_3,d0_26_2,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_7_3,d2_8_2,d2_9_1,d3_16_3,d3_17_2,d3_18_1,d3_19_0,d4_26_3]
  ring
#print axioms coefficient_26_3
compact_certificate_declaration theorem coefficient_26_4 (y z w b u : ℂ) :
    (innerCertificate26 y z w b u)[4]?=some 0 := by
  change some ((((((d0_23_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_24_4 y z w b u)*(d1_2_0 y z w b u))+0)+((d0_25_3 y z w b u)*(d1_1_1 y z w b u))))+((-1)*(d4_26_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_23_4,d0_24_4,d0_25_3,d1_1_1,d1_2_0,d1_3_0,d4_26_4]
  ring
#print axioms coefficient_26_4
compact_certificate_declaration theorem coefficient_26_5 (y z w b u : ℂ) :
    (innerCertificate26 y z w b u)[5]?=some 0 := by
  change some (((((d0_23_5 y z w b u)*(d1_3_0 y z w b u))+0)+((-1)*(d4_26_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_23_5,d1_3_0,d4_26_5]
  ring
#print axioms coefficient_26_5

end SmallLevelTwentySixMMPPariTrace026
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_27 (y z w b u : ℂ) : (innerCertificate27 y z w b u).length=5 := by
  norm_num [innerCertificate27,add,multiply,scale,inner0_24,inner0_25,inner0_26,inner0_27,inner1_0,inner1_1,inner1_2,inner1_3,inner2_10,inner2_8,inner2_9,inner3_17,inner3_18,inner3_19,inner4_27]
compact_certificate_declaration theorem inner_eval_27 (y z w a b u : ℂ) :
    evaluate a (innerCertificate27 y z w b u)=(((((c0_24 y z w a b u)*(c1_3 y z w a b u))+(((c0_25 y z w a b u)*(c1_2 y z w a b u))+(((c0_26 y z w a b u)*(c1_1 y z w a b u))+(((c0_27 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_8 y z w a b u)*(c3_19 y z w a b u))+(((c2_9 y z w a b u)*(c3_18 y z w a b u))+((c2_10 y z w a b u)*(c3_17 y z w a b u)))))+((-1)*(c4_27 y z w a b u))) := by
  simp only [innerCertificate27,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_24,c0_25,c0_26,c0_27,c1_0,c1_1,c1_2,c1_3,c2_10,c2_8,c2_9,c3_17,c3_18,c3_19,c4_27]
#print axioms inner_eval_27

end SmallLevelTwentySixMMPPariTrace026
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_27_0 (y z w b u : ℂ) :
    (innerCertificate27 y z w b u)[0]?=some 0 := by
  change some (((((((d0_24_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_25_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_26_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_27_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_8_0 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_9_0 y z w b u)*(d3_18_0 y z w b u))+0)+(((d2_10_0 y z w b u)*(d3_17_0 y z w b u))+0))))+(((-1)*(d4_27_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_24_0,d0_25_0,d0_26_0,d0_27_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_10_0,d2_8_0,d2_9_0,d3_17_0,d3_18_0,d3_19_0,d4_27_0]
  ring
#print axioms coefficient_27_0
compact_certificate_declaration theorem coefficient_27_1 (y z w b u : ℂ) :
    (innerCertificate27 y z w b u)[1]?=some 0 := by
  change some (((((((d0_24_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_25_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_26_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_26_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_27_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_27_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_8_1 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_9_0 y z w b u)*(d3_18_1 y z w b u))+(((d2_9_1 y z w b u)*(d3_18_0 y z w b u))+0))+((d2_10_0 y z w b u)*(d3_17_1 y z w b u)))))+((-1)*(d4_27_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_24_1,d0_25_1,d0_26_0,d0_26_1,d0_27_0,d0_27_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_8_1,d2_9_0,d2_9_1,d3_17_1,d3_18_0,d3_18_1,d3_19_0,d4_27_1]
  ring
#print axioms coefficient_27_1
compact_certificate_declaration theorem coefficient_27_2 (y z w b u : ℂ) :
    (innerCertificate27 y z w b u)[2]?=some 0 := by
  change some (((((((d0_24_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_25_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_26_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_26_2 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_27_1 y z w b u)*(d1_0_1 y z w b u)))))+((((d2_8_2 y z w b u)*(d3_19_0 y z w b u))+0)+(((d2_9_1 y z w b u)*(d3_18_1 y z w b u))+((d2_10_0 y z w b u)*(d3_17_2 y z w b u)))))+((-1)*(d4_27_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_24_2,d0_25_2,d0_26_1,d0_26_2,d0_27_1,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_8_2,d2_9_1,d3_17_2,d3_18_1,d3_19_0,d4_27_2]
  ring
#print axioms coefficient_27_2

compact_certificate_declaration theorem coefficient_27_3 (y z w b u : ℂ) :
    (innerCertificate27 y z w b u)[3]?=some 0 := by
  change some ((((((d0_24_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_25_3 y z w b u)*(d1_2_0 y z w b u))+0)+((d0_26_2 y z w b u)*(d1_1_1 y z w b u))))+((-1)*(d4_27_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_24_3,d0_25_3,d0_26_2,d1_1_1,d1_2_0,d1_3_0,d4_27_3]
  ring
#print axioms coefficient_27_3
compact_certificate_declaration theorem coefficient_27_4 (y z w b u : ℂ) :
    (innerCertificate27 y z w b u)[4]?=some 0 := by
  change some (((((d0_24_4 y z w b u)*(d1_3_0 y z w b u))+0)+((-1)*(d4_27_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_24_4,d1_3_0,d4_27_4]
  ring
#print axioms coefficient_27_4

end SmallLevelTwentySixMMPPariTrace026
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_28 (y z w b u : ℂ) : (innerCertificate28 y z w b u).length=4 := by
  norm_num [innerCertificate28,add,multiply,scale,inner0_25,inner0_26,inner0_27,inner0_28,inner1_0,inner1_1,inner1_2,inner1_3,inner2_10,inner2_9,inner3_18,inner3_19,inner4_28]
compact_certificate_declaration theorem inner_eval_28 (y z w a b u : ℂ) :
    evaluate a (innerCertificate28 y z w b u)=(((((c0_25 y z w a b u)*(c1_3 y z w a b u))+(((c0_26 y z w a b u)*(c1_2 y z w a b u))+(((c0_27 y z w a b u)*(c1_1 y z w a b u))+(((c0_28 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_9 y z w a b u)*(c3_19 y z w a b u))+((c2_10 y z w a b u)*(c3_18 y z w a b u))))+((-1)*(c4_28 y z w a b u))) := by
  simp only [innerCertificate28,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_25,c0_26,c0_27,c0_28,c1_0,c1_1,c1_2,c1_3,c2_10,c2_9,c3_18,c3_19,c4_28]
#print axioms inner_eval_28

end SmallLevelTwentySixMMPPariTrace026
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_28_0 (y z w b u : ℂ) :
    (innerCertificate28 y z w b u)[0]?=some 0 := by
  change some (((((((d0_25_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_26_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_27_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_28_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_9_0 y z w b u)*(d3_19_0 y z w b u))+0)+(((d2_10_0 y z w b u)*(d3_18_0 y z w b u))+0)))+(((-1)*(d4_28_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_25_0,d0_26_0,d0_27_0,d0_28_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_10_0,d2_9_0,d3_18_0,d3_19_0,d4_28_0]
  ring
#print axioms coefficient_28_0
compact_certificate_declaration theorem coefficient_28_1 (y z w b u : ℂ) :
    (innerCertificate28 y z w b u)[1]?=some 0 := by
  change some (((((((d0_25_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_26_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_27_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_27_1 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_28_0 y z w b u)*(d1_0_1 y z w b u)))))+((((d2_9_1 y z w b u)*(d3_19_0 y z w b u))+0)+((d2_10_0 y z w b u)*(d3_18_1 y z w b u))))+((-1)*(d4_28_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_25_1,d0_26_1,d0_27_0,d0_27_1,d0_28_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_9_1,d3_18_1,d3_19_0,d4_28_1]
  ring
#print axioms coefficient_28_1
compact_certificate_declaration theorem coefficient_28_2 (y z w b u : ℂ) :
    (innerCertificate28 y z w b u)[2]?=some 0 := by
  change some ((((((d0_25_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_26_2 y z w b u)*(d1_2_0 y z w b u))+0)+((d0_27_1 y z w b u)*(d1_1_1 y z w b u))))+((-1)*(d4_28_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_25_2,d0_26_2,d0_27_1,d1_1_1,d1_2_0,d1_3_0,d4_28_2]
  ring
#print axioms coefficient_28_2

compact_certificate_declaration theorem coefficient_28_3 (y z w b u : ℂ) :
    (innerCertificate28 y z w b u)[3]?=some 0 := by
  change some (((((d0_25_3 y z w b u)*(d1_3_0 y z w b u))+0)+((-1)*(d4_28_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_25_3,d1_3_0,d4_28_3]
  ring
#print axioms coefficient_28_3

end SmallLevelTwentySixMMPPariTrace026
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_29 (y z w b u : ℂ) : (innerCertificate29 y z w b u).length=3 := by
  norm_num [innerCertificate29,add,multiply,scale,inner0_26,inner0_27,inner0_28,inner1_1,inner1_2,inner1_3,inner2_10,inner3_19,inner4_29]
compact_certificate_declaration theorem inner_eval_29 (y z w a b u : ℂ) :
    evaluate a (innerCertificate29 y z w b u)=(((((c0_26 y z w a b u)*(c1_3 y z w a b u))+(((c0_27 y z w a b u)*(c1_2 y z w a b u))+((c0_28 y z w a b u)*(c1_1 y z w a b u))))+((c2_10 y z w a b u)*(c3_19 y z w a b u)))+((-1)*(c4_29 y z w a b u))) := by
  simp only [innerCertificate29,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_26,c0_27,c0_28,c1_1,c1_2,c1_3,c2_10,c3_19,c4_29]
#print axioms inner_eval_29

end SmallLevelTwentySixMMPPariTrace026
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem coefficient_29_0 (y z w b u : ℂ) :
    (innerCertificate29 y z w b u)[0]?=some 0 := by
  change some (((((((d0_26_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_27_0 y z w b u)*(d1_2_0 y z w b u))+0)+(((d0_28_0 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d2_10_0 y z w b u)*(d3_19_0 y z w b u))+0))+(((-1)*(d4_29_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_26_0,d0_27_0,d0_28_0,d1_1_0,d1_2_0,d1_3_0,d2_10_0,d3_19_0,d4_29_0]
  ring
#print axioms coefficient_29_0
compact_certificate_declaration theorem coefficient_29_1 (y z w b u : ℂ) :
    (innerCertificate29 y z w b u)[1]?=some 0 := by
  change some ((((((d0_26_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_27_1 y z w b u)*(d1_2_0 y z w b u))+0)+((d0_28_0 y z w b u)*(d1_1_1 y z w b u))))+((-1)*(d4_29_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_26_1,d0_27_1,d0_28_0,d1_1_1,d1_2_0,d1_3_0,d4_29_1]
  ring
#print axioms coefficient_29_1
compact_certificate_declaration theorem coefficient_29_2 (y z w b u : ℂ) :
    (innerCertificate29 y z w b u)[2]?=some 0 := by
  change some (((((d0_26_2 y z w b u)*(d1_3_0 y z w b u))+0)+((-1)*(d4_29_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_26_2,d1_3_0,d4_29_2]
  ring
#print axioms coefficient_29_2

end SmallLevelTwentySixMMPPariTrace026
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_30 (y z w b u : ℂ) : (innerCertificate30 y z w b u).length=2 := by
  norm_num [innerCertificate30,add,multiply,scale,inner0_27,inner0_28,inner1_2,inner1_3,inner4_30]
compact_certificate_declaration theorem inner_eval_30 (y z w a b u : ℂ) :
    evaluate a (innerCertificate30 y z w b u)=((((c0_27 y z w a b u)*(c1_3 y z w a b u))+((c0_28 y z w a b u)*(c1_2 y z w a b u)))+((-1)*(c4_30 y z w a b u))) := by
  simp only [innerCertificate30,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_27,c0_28,c1_2,c1_3,c4_30]
#print axioms inner_eval_30

end SmallLevelTwentySixMMPPariTrace026
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem coefficient_30_0 (y z w b u : ℂ) :
    (innerCertificate30 y z w b u)[0]?=some 0 := by
  change some ((((((d0_27_0 y z w b u)*(d1_3_0 y z w b u))+0)+(((d0_28_0 y z w b u)*(d1_2_0 y z w b u))+0))+(((-1)*(d4_30_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_27_0,d0_28_0,d1_2_0,d1_3_0,d4_30_0]
  ring
#print axioms coefficient_30_0
compact_certificate_declaration theorem coefficient_30_1 (y z w b u : ℂ) :
    (innerCertificate30 y z w b u)[1]?=some 0 := by
  change some (((((d0_27_1 y z w b u)*(d1_3_0 y z w b u))+0)+((-1)*(d4_30_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_27_1,d1_3_0,d4_30_1]
  ring
#print axioms coefficient_30_1

end SmallLevelTwentySixMMPPariTrace026
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_31 (y z w b u : ℂ) : (innerCertificate31 y z w b u).length=1 := by
  norm_num [innerCertificate31,add,multiply,scale,inner0_28,inner1_3,inner4_31]
compact_certificate_declaration theorem inner_eval_31 (y z w a b u : ℂ) :
    evaluate a (innerCertificate31 y z w b u)=(((c0_28 y z w a b u)*(c1_3 y z w a b u))+((-1)*(c4_31 y z w a b u))) := by
  simp only [innerCertificate31,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_28,c1_3,c4_31]
#print axioms inner_eval_31

end SmallLevelTwentySixMMPPariTrace026
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem coefficient_31_0 (y z w b u : ℂ) :
    (innerCertificate31 y z w b u)[0]?=some 0 := by
  change some (((((d0_28_0 y z w b u)*(d1_3_0 y z w b u))+0)+(((-1)*(d4_31_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_28_0,d1_3_0,d4_31_0]
  ring
#print axioms coefficient_31_0

end SmallLevelTwentySixMMPPariTrace026
end

end

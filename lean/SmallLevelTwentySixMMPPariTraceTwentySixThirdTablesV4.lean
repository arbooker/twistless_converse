module
public import SmallLevelTwentySixMMPPariTraceTwentySixLowTablesV4
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
compact_certificate_declaration theorem inner_length_16 (y z w b u : ℂ) : (innerCertificate16 y z w b u).length=12 := by
  norm_num [innerCertificate16,add,multiply,scale,inner0_13,inner0_14,inner0_15,inner0_16,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_6,inner3_7,inner3_8,inner3_9,inner4_16]
compact_certificate_declaration theorem inner_eval_16 (y z w a b u : ℂ) :
    evaluate a (innerCertificate16 y z w b u)=(((((c0_13 y z w a b u)*(c1_3 y z w a b u))+(((c0_14 y z w a b u)*(c1_2 y z w a b u))+(((c0_15 y z w a b u)*(c1_1 y z w a b u))+(((c0_16 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_16 y z w a b u))+(((c2_1 y z w a b u)*(c3_15 y z w a b u))+(((c2_2 y z w a b u)*(c3_14 y z w a b u))+(((c2_3 y z w a b u)*(c3_13 y z w a b u))+(((c2_4 y z w a b u)*(c3_12 y z w a b u))+(((c2_5 y z w a b u)*(c3_11 y z w a b u))+(((c2_6 y z w a b u)*(c3_10 y z w a b u))+(((c2_7 y z w a b u)*(c3_9 y z w a b u))+(((c2_8 y z w a b u)*(c3_8 y z w a b u))+(((c2_9 y z w a b u)*(c3_7 y z w a b u))+((c2_10 y z w a b u)*(c3_6 y z w a b u)))))))))))))+((-1)*(c4_16 y z w a b u))) := by
  simp only [innerCertificate16,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_13,c0_14,c0_15,c0_16,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_10,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_6,c3_7,c3_8,c3_9,c4_16]
#print axioms inner_eval_16

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

compact_certificate_declaration theorem coefficient_16_0 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[0]?=some 0 := by
  change some (((((((d0_13_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_16_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_16_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_15_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_14_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_13_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_12_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_11_0 y z w b u))+0)+((((d2_6_0 y z w b u)*(d3_10_0 y z w b u))+0)+((((d2_7_0 y z w b u)*(d3_9_0 y z w b u))+0)+((((d2_8_0 y z w b u)*(d3_8_0 y z w b u))+0)+((((d2_9_0 y z w b u)*(d3_7_0 y z w b u))+0)+(((d2_10_0 y z w b u)*(d3_6_0 y z w b u))+0))))))))))))+(((-1)*(d4_16_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_0,d0_14_0,d0_15_0,d0_16_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_10_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d2_7_0,d2_8_0,d2_9_0,d3_10_0,d3_11_0,d3_12_0,d3_13_0,d3_14_0,d3_15_0,d3_16_0,d3_6_0,d3_7_0,d3_8_0,d3_9_0,d4_16_0]
  ring
#print axioms coefficient_16_0
compact_certificate_declaration theorem coefficient_16_1 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[1]?=some 0 := by
  change some (((((((d0_13_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_15_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_16_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_16_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_16_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_16_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_15_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_15_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_14_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_14_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_13_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_13_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_12_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_12_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_11_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_11_0 y z w b u))+0))+((((d2_6_0 y z w b u)*(d3_10_1 y z w b u))+(((d2_6_1 y z w b u)*(d3_10_0 y z w b u))+0))+((((d2_7_0 y z w b u)*(d3_9_1 y z w b u))+(((d2_7_1 y z w b u)*(d3_9_0 y z w b u))+0))+((((d2_8_0 y z w b u)*(d3_8_1 y z w b u))+(((d2_8_1 y z w b u)*(d3_8_0 y z w b u))+0))+((((d2_9_0 y z w b u)*(d3_7_1 y z w b u))+(((d2_9_1 y z w b u)*(d3_7_0 y z w b u))+0))+((d2_10_0 y z w b u)*(d3_6_1 y z w b u)))))))))))))+((-1)*(d4_16_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_1,d0_14_1,d0_15_0,d0_15_1,d0_16_0,d0_16_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_10_0,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d2_6_1,d2_7_0,d2_7_1,d2_8_0,d2_8_1,d2_9_0,d2_9_1,d3_10_0,d3_10_1,d3_11_0,d3_11_1,d3_12_0,d3_12_1,d3_13_0,d3_13_1,d3_14_0,d3_14_1,d3_15_0,d3_15_1,d3_16_0,d3_16_1,d3_6_1,d3_7_0,d3_7_1,d3_8_0,d3_8_1,d3_9_0,d3_9_1,d4_16_1]
  ring
#print axioms coefficient_16_1

compact_certificate_declaration theorem coefficient_16_2 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[2]?=some 0 := by
  change some (((((((d0_13_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_15_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_16_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_16_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_16_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_16_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_15_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_15_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_15_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_14_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_14_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_14_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_13_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_13_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_13_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_12_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_12_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_12_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_11_2 y z w b u))+(((d2_5_1 y z w b u)*(d3_11_1 y z w b u))+(((d2_5_2 y z w b u)*(d3_11_0 y z w b u))+0)))+((((d2_6_0 y z w b u)*(d3_10_2 y z w b u))+(((d2_6_1 y z w b u)*(d3_10_1 y z w b u))+(((d2_6_2 y z w b u)*(d3_10_0 y z w b u))+0)))+((((d2_7_0 y z w b u)*(d3_9_2 y z w b u))+(((d2_7_1 y z w b u)*(d3_9_1 y z w b u))+(((d2_7_2 y z w b u)*(d3_9_0 y z w b u))+0)))+((((d2_8_0 y z w b u)*(d3_8_2 y z w b u))+(((d2_8_1 y z w b u)*(d3_8_1 y z w b u))+(((d2_8_2 y z w b u)*(d3_8_0 y z w b u))+0)))+((((d2_9_0 y z w b u)*(d3_7_2 y z w b u))+((d2_9_1 y z w b u)*(d3_7_1 y z w b u)))+((d2_10_0 y z w b u)*(d3_6_2 y z w b u)))))))))))))+((-1)*(d4_16_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_2,d0_14_2,d0_15_1,d0_15_2,d0_16_1,d0_16_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_10_0,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_5_2,d2_6_0,d2_6_1,d2_6_2,d2_7_0,d2_7_1,d2_7_2,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_0,d3_10_1,d3_10_2,d3_11_0,d3_11_1,d3_11_2,d3_12_0,d3_12_1,d3_12_2,d3_13_0,d3_13_1,d3_13_2,d3_14_0,d3_14_1,d3_14_2,d3_15_0,d3_15_1,d3_15_2,d3_16_0,d3_16_1,d3_16_2,d3_6_2,d3_7_1,d3_7_2,d3_8_0,d3_8_1,d3_8_2,d3_9_0,d3_9_1,d3_9_2,d4_16_2]
  ring
#print axioms coefficient_16_2

compact_certificate_declaration theorem coefficient_16_3 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[3]?=some 0 := by
  change some (((((((d0_13_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_15_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_16_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_16_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_16_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_16_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_16_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_15_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_15_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_15_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_15_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_14_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_14_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_14_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_14_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_13_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_13_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_13_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_13_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_12_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_12_2 y z w b u))+(((d2_4_2 y z w b u)*(d3_12_1 y z w b u))+(((d2_4_3 y z w b u)*(d3_12_0 y z w b u))+0))))+((((d2_5_0 y z w b u)*(d3_11_3 y z w b u))+(((d2_5_1 y z w b u)*(d3_11_2 y z w b u))+(((d2_5_2 y z w b u)*(d3_11_1 y z w b u))+(((d2_5_3 y z w b u)*(d3_11_0 y z w b u))+0))))+((((d2_6_0 y z w b u)*(d3_10_3 y z w b u))+(((d2_6_1 y z w b u)*(d3_10_2 y z w b u))+(((d2_6_2 y z w b u)*(d3_10_1 y z w b u))+(((d2_6_3 y z w b u)*(d3_10_0 y z w b u))+0))))+((((d2_7_0 y z w b u)*(d3_9_3 y z w b u))+(((d2_7_1 y z w b u)*(d3_9_2 y z w b u))+(((d2_7_2 y z w b u)*(d3_9_1 y z w b u))+(((d2_7_3 y z w b u)*(d3_9_0 y z w b u))+0))))+((((d2_8_0 y z w b u)*(d3_8_3 y z w b u))+(((d2_8_1 y z w b u)*(d3_8_2 y z w b u))+((d2_8_2 y z w b u)*(d3_8_1 y z w b u))))+((((d2_9_0 y z w b u)*(d3_7_3 y z w b u))+((d2_9_1 y z w b u)*(d3_7_2 y z w b u)))+((d2_10_0 y z w b u)*(d3_6_3 y z w b u)))))))))))))+((-1)*(d4_16_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_3,d0_14_3,d0_15_2,d0_15_3,d0_16_2,d0_16_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_10_0,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_0,d3_10_1,d3_10_2,d3_10_3,d3_11_0,d3_11_1,d3_11_2,d3_11_3,d3_12_0,d3_12_1,d3_12_2,d3_12_3,d3_13_0,d3_13_1,d3_13_2,d3_13_3,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_6_3,d3_7_2,d3_7_3,d3_8_1,d3_8_2,d3_8_3,d3_9_0,d3_9_1,d3_9_2,d3_9_3,d4_16_3]
  ring
#print axioms coefficient_16_3

compact_certificate_declaration theorem coefficient_16_4 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[4]?=some 0 := by
  change some (((((((d0_13_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_15_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_16_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_16_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_16_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_16_2 y z w b u))+(((d2_0_3 y z w b u)*(d3_16_1 y z w b u))+(((d2_0_4 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_15_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_15_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_15_2 y z w b u))+(((d2_1_3 y z w b u)*(d3_15_1 y z w b u))+(((d2_1_4 y z w b u)*(d3_15_0 y z w b u))+0)))))+((((d2_2_0 y z w b u)*(d3_14_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_14_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_14_2 y z w b u))+(((d2_2_3 y z w b u)*(d3_14_1 y z w b u))+(((d2_2_4 y z w b u)*(d3_14_0 y z w b u))+0)))))+((((d2_3_0 y z w b u)*(d3_13_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_13_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_13_2 y z w b u))+(((d2_3_3 y z w b u)*(d3_13_1 y z w b u))+(((d2_3_4 y z w b u)*(d3_13_0 y z w b u))+0)))))+((((d2_4_0 y z w b u)*(d3_12_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_12_3 y z w b u))+(((d2_4_2 y z w b u)*(d3_12_2 y z w b u))+(((d2_4_3 y z w b u)*(d3_12_1 y z w b u))+(((d2_4_4 y z w b u)*(d3_12_0 y z w b u))+0)))))+((((d2_5_0 y z w b u)*(d3_11_4 y z w b u))+(((d2_5_1 y z w b u)*(d3_11_3 y z w b u))+(((d2_5_2 y z w b u)*(d3_11_2 y z w b u))+(((d2_5_3 y z w b u)*(d3_11_1 y z w b u))+(((d2_5_4 y z w b u)*(d3_11_0 y z w b u))+0)))))+((((d2_6_0 y z w b u)*(d3_10_4 y z w b u))+(((d2_6_1 y z w b u)*(d3_10_3 y z w b u))+(((d2_6_2 y z w b u)*(d3_10_2 y z w b u))+(((d2_6_3 y z w b u)*(d3_10_1 y z w b u))+(((d2_6_4 y z w b u)*(d3_10_0 y z w b u))+0)))))+((((d2_7_0 y z w b u)*(d3_9_4 y z w b u))+(((d2_7_1 y z w b u)*(d3_9_3 y z w b u))+(((d2_7_2 y z w b u)*(d3_9_2 y z w b u))+((d2_7_3 y z w b u)*(d3_9_1 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_8_4 y z w b u))+(((d2_8_1 y z w b u)*(d3_8_3 y z w b u))+((d2_8_2 y z w b u)*(d3_8_2 y z w b u))))+((((d2_9_0 y z w b u)*(d3_7_4 y z w b u))+((d2_9_1 y z w b u)*(d3_7_3 y z w b u)))+((d2_10_0 y z w b u)*(d3_6_4 y z w b u)))))))))))))+((-1)*(d4_16_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_4,d0_14_4,d0_15_3,d0_15_4,d0_16_3,d0_16_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_10_0,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_0,d3_10_1,d3_10_2,d3_10_3,d3_10_4,d3_11_0,d3_11_1,d3_11_2,d3_11_3,d3_11_4,d3_12_0,d3_12_1,d3_12_2,d3_12_3,d3_12_4,d3_13_0,d3_13_1,d3_13_2,d3_13_3,d3_13_4,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_6_4,d3_7_3,d3_7_4,d3_8_2,d3_8_3,d3_8_4,d3_9_1,d3_9_2,d3_9_3,d3_9_4,d4_16_4]
  ring
#print axioms coefficient_16_4

compact_certificate_declaration theorem coefficient_16_5 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[5]?=some 0 := by
  change some (((((((d0_13_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_15_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_16_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_16_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_16_3 y z w b u))+(((d2_0_3 y z w b u)*(d3_16_2 y z w b u))+(((d2_0_4 y z w b u)*(d3_16_1 y z w b u))+(((d2_0_5 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_1_1 y z w b u)*(d3_15_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_15_3 y z w b u))+(((d2_1_3 y z w b u)*(d3_15_2 y z w b u))+(((d2_1_4 y z w b u)*(d3_15_1 y z w b u))+(((d2_1_5 y z w b u)*(d3_15_0 y z w b u))+0)))))+((((d2_2_1 y z w b u)*(d3_14_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_14_3 y z w b u))+(((d2_2_3 y z w b u)*(d3_14_2 y z w b u))+(((d2_2_4 y z w b u)*(d3_14_1 y z w b u))+(((d2_2_5 y z w b u)*(d3_14_0 y z w b u))+0)))))+((((d2_3_0 y z w b u)*(d3_13_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_13_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_13_3 y z w b u))+(((d2_3_3 y z w b u)*(d3_13_2 y z w b u))+(((d2_3_4 y z w b u)*(d3_13_1 y z w b u))+(((d2_3_5 y z w b u)*(d3_13_0 y z w b u))+0))))))+((((d2_4_0 y z w b u)*(d3_12_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_12_4 y z w b u))+(((d2_4_2 y z w b u)*(d3_12_3 y z w b u))+(((d2_4_3 y z w b u)*(d3_12_2 y z w b u))+(((d2_4_4 y z w b u)*(d3_12_1 y z w b u))+(((d2_4_5 y z w b u)*(d3_12_0 y z w b u))+0))))))+((((d2_5_0 y z w b u)*(d3_11_5 y z w b u))+(((d2_5_1 y z w b u)*(d3_11_4 y z w b u))+(((d2_5_2 y z w b u)*(d3_11_3 y z w b u))+(((d2_5_3 y z w b u)*(d3_11_2 y z w b u))+(((d2_5_4 y z w b u)*(d3_11_1 y z w b u))+(((d2_5_5 y z w b u)*(d3_11_0 y z w b u))+0))))))+((((d2_6_0 y z w b u)*(d3_10_5 y z w b u))+(((d2_6_1 y z w b u)*(d3_10_4 y z w b u))+(((d2_6_2 y z w b u)*(d3_10_3 y z w b u))+(((d2_6_3 y z w b u)*(d3_10_2 y z w b u))+((d2_6_4 y z w b u)*(d3_10_1 y z w b u))))))+((((d2_7_0 y z w b u)*(d3_9_5 y z w b u))+(((d2_7_1 y z w b u)*(d3_9_4 y z w b u))+(((d2_7_2 y z w b u)*(d3_9_3 y z w b u))+((d2_7_3 y z w b u)*(d3_9_2 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_8_5 y z w b u))+(((d2_8_1 y z w b u)*(d3_8_4 y z w b u))+((d2_8_2 y z w b u)*(d3_8_3 y z w b u))))+((((d2_9_0 y z w b u)*(d3_7_5 y z w b u))+((d2_9_1 y z w b u)*(d3_7_4 y z w b u)))+((d2_10_0 y z w b u)*(d3_6_5 y z w b u)))))))))))))+((-1)*(d4_16_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_5,d0_14_5,d0_15_4,d0_15_5,d0_16_4,d0_16_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_10_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_1,d3_10_2,d3_10_3,d3_10_4,d3_10_5,d3_11_0,d3_11_1,d3_11_2,d3_11_3,d3_11_4,d3_11_5,d3_12_0,d3_12_1,d3_12_2,d3_12_3,d3_12_4,d3_12_5,d3_13_0,d3_13_1,d3_13_2,d3_13_3,d3_13_4,d3_13_5,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_6_5,d3_7_4,d3_7_5,d3_8_3,d3_8_4,d3_8_5,d3_9_2,d3_9_3,d3_9_4,d3_9_5,d4_16_5]
  ring
#print axioms coefficient_16_5
compact_certificate_declaration theorem coefficient_16_6 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[6]?=some 0 := by
  change some (((((((d0_13_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_15_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_16_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_16_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_3 y z w b u)*(d3_16_3 y z w b u))+(((d2_0_4 y z w b u)*(d3_16_2 y z w b u))+((d2_0_5 y z w b u)*(d3_16_1 y z w b u))))+((((d2_1_2 y z w b u)*(d3_15_4 y z w b u))+(((d2_1_3 y z w b u)*(d3_15_3 y z w b u))+(((d2_1_4 y z w b u)*(d3_15_2 y z w b u))+((d2_1_5 y z w b u)*(d3_15_1 y z w b u)))))+((((d2_2_2 y z w b u)*(d3_14_4 y z w b u))+(((d2_2_3 y z w b u)*(d3_14_3 y z w b u))+(((d2_2_4 y z w b u)*(d3_14_2 y z w b u))+((d2_2_5 y z w b u)*(d3_14_1 y z w b u)))))+((((d2_3_1 y z w b u)*(d3_13_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_13_4 y z w b u))+(((d2_3_3 y z w b u)*(d3_13_3 y z w b u))+(((d2_3_4 y z w b u)*(d3_13_2 y z w b u))+((d2_3_5 y z w b u)*(d3_13_1 y z w b u))))))+((((d2_4_0 y z w b u)*(d3_12_6 y z w b u))+(((d2_4_1 y z w b u)*(d3_12_5 y z w b u))+(((d2_4_2 y z w b u)*(d3_12_4 y z w b u))+(((d2_4_3 y z w b u)*(d3_12_3 y z w b u))+(((d2_4_4 y z w b u)*(d3_12_2 y z w b u))+((d2_4_5 y z w b u)*(d3_12_1 y z w b u)))))))+((((d2_5_0 y z w b u)*(d3_11_6 y z w b u))+(((d2_5_1 y z w b u)*(d3_11_5 y z w b u))+(((d2_5_2 y z w b u)*(d3_11_4 y z w b u))+(((d2_5_3 y z w b u)*(d3_11_3 y z w b u))+(((d2_5_4 y z w b u)*(d3_11_2 y z w b u))+((d2_5_5 y z w b u)*(d3_11_1 y z w b u)))))))+((((d2_6_0 y z w b u)*(d3_10_6 y z w b u))+(((d2_6_1 y z w b u)*(d3_10_5 y z w b u))+(((d2_6_2 y z w b u)*(d3_10_4 y z w b u))+(((d2_6_3 y z w b u)*(d3_10_3 y z w b u))+((d2_6_4 y z w b u)*(d3_10_2 y z w b u))))))+((((d2_7_0 y z w b u)*(d3_9_6 y z w b u))+(((d2_7_1 y z w b u)*(d3_9_5 y z w b u))+(((d2_7_2 y z w b u)*(d3_9_4 y z w b u))+((d2_7_3 y z w b u)*(d3_9_3 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_8_6 y z w b u))+(((d2_8_1 y z w b u)*(d3_8_5 y z w b u))+((d2_8_2 y z w b u)*(d3_8_4 y z w b u))))+((((d2_9_0 y z w b u)*(d3_7_6 y z w b u))+((d2_9_1 y z w b u)*(d3_7_5 y z w b u)))+((d2_10_0 y z w b u)*(d3_6_6 y z w b u)))))))))))))+((-1)*(d4_16_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_6,d0_14_6,d0_15_5,d0_15_6,d0_16_5,d0_16_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_0_4,d2_0_5,d2_10_0,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_2,d3_10_3,d3_10_4,d3_10_5,d3_10_6,d3_11_1,d3_11_2,d3_11_3,d3_11_4,d3_11_5,d3_11_6,d3_12_1,d3_12_2,d3_12_3,d3_12_4,d3_12_5,d3_12_6,d3_13_1,d3_13_2,d3_13_3,d3_13_4,d3_13_5,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_1,d3_16_2,d3_16_3,d3_6_6,d3_7_5,d3_7_6,d3_8_4,d3_8_5,d3_8_6,d3_9_3,d3_9_4,d3_9_5,d3_9_6,d4_16_6]
  ring
#print axioms coefficient_16_6

compact_certificate_declaration theorem coefficient_16_7 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[7]?=some 0 := by
  change some (((((((d0_13_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_15_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_16_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_16_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_4 y z w b u)*(d3_16_3 y z w b u))+((d2_0_5 y z w b u)*(d3_16_2 y z w b u)))+((((d2_1_3 y z w b u)*(d3_15_4 y z w b u))+(((d2_1_4 y z w b u)*(d3_15_3 y z w b u))+((d2_1_5 y z w b u)*(d3_15_2 y z w b u))))+((((d2_2_3 y z w b u)*(d3_14_4 y z w b u))+(((d2_2_4 y z w b u)*(d3_14_3 y z w b u))+((d2_2_5 y z w b u)*(d3_14_2 y z w b u))))+((((d2_3_2 y z w b u)*(d3_13_5 y z w b u))+(((d2_3_3 y z w b u)*(d3_13_4 y z w b u))+(((d2_3_4 y z w b u)*(d3_13_3 y z w b u))+((d2_3_5 y z w b u)*(d3_13_2 y z w b u)))))+((((d2_4_1 y z w b u)*(d3_12_6 y z w b u))+(((d2_4_2 y z w b u)*(d3_12_5 y z w b u))+(((d2_4_3 y z w b u)*(d3_12_4 y z w b u))+(((d2_4_4 y z w b u)*(d3_12_3 y z w b u))+((d2_4_5 y z w b u)*(d3_12_2 y z w b u))))))+((((d2_5_1 y z w b u)*(d3_11_6 y z w b u))+(((d2_5_2 y z w b u)*(d3_11_5 y z w b u))+(((d2_5_3 y z w b u)*(d3_11_4 y z w b u))+(((d2_5_4 y z w b u)*(d3_11_3 y z w b u))+((d2_5_5 y z w b u)*(d3_11_2 y z w b u))))))+((((d2_6_0 y z w b u)*(d3_10_7 y z w b u))+(((d2_6_1 y z w b u)*(d3_10_6 y z w b u))+(((d2_6_2 y z w b u)*(d3_10_5 y z w b u))+(((d2_6_3 y z w b u)*(d3_10_4 y z w b u))+((d2_6_4 y z w b u)*(d3_10_3 y z w b u))))))+((((d2_7_0 y z w b u)*(d3_9_7 y z w b u))+(((d2_7_1 y z w b u)*(d3_9_6 y z w b u))+(((d2_7_2 y z w b u)*(d3_9_5 y z w b u))+((d2_7_3 y z w b u)*(d3_9_4 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_8_7 y z w b u))+(((d2_8_1 y z w b u)*(d3_8_6 y z w b u))+((d2_8_2 y z w b u)*(d3_8_5 y z w b u))))+((((d2_9_0 y z w b u)*(d3_7_7 y z w b u))+((d2_9_1 y z w b u)*(d3_7_6 y z w b u)))+((d2_10_0 y z w b u)*(d3_6_7 y z w b u)))))))))))))+((-1)*(d4_16_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_7,d0_14_7,d0_15_6,d0_15_7,d0_16_6,d0_16_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_4,d2_0_5,d2_10_0,d2_1_3,d2_1_4,d2_1_5,d2_2_3,d2_2_4,d2_2_5,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_3,d3_10_4,d3_10_5,d3_10_6,d3_10_7,d3_11_2,d3_11_3,d3_11_4,d3_11_5,d3_11_6,d3_12_2,d3_12_3,d3_12_4,d3_12_5,d3_12_6,d3_13_2,d3_13_3,d3_13_4,d3_13_5,d3_14_2,d3_14_3,d3_14_4,d3_15_2,d3_15_3,d3_15_4,d3_16_2,d3_16_3,d3_6_7,d3_7_6,d3_7_7,d3_8_5,d3_8_6,d3_8_7,d3_9_4,d3_9_5,d3_9_6,d3_9_7,d4_16_7]
  ring
#print axioms coefficient_16_7
compact_certificate_declaration theorem coefficient_16_8 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[8]?=some 0 := by
  change some (((((((d0_13_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_15_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_16_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_16_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_0_5 y z w b u)*(d3_16_3 y z w b u))+((((d2_1_4 y z w b u)*(d3_15_4 y z w b u))+((d2_1_5 y z w b u)*(d3_15_3 y z w b u)))+((((d2_2_4 y z w b u)*(d3_14_4 y z w b u))+((d2_2_5 y z w b u)*(d3_14_3 y z w b u)))+((((d2_3_3 y z w b u)*(d3_13_5 y z w b u))+(((d2_3_4 y z w b u)*(d3_13_4 y z w b u))+((d2_3_5 y z w b u)*(d3_13_3 y z w b u))))+((((d2_4_2 y z w b u)*(d3_12_6 y z w b u))+(((d2_4_3 y z w b u)*(d3_12_5 y z w b u))+(((d2_4_4 y z w b u)*(d3_12_4 y z w b u))+((d2_4_5 y z w b u)*(d3_12_3 y z w b u)))))+((((d2_5_2 y z w b u)*(d3_11_6 y z w b u))+(((d2_5_3 y z w b u)*(d3_11_5 y z w b u))+(((d2_5_4 y z w b u)*(d3_11_4 y z w b u))+((d2_5_5 y z w b u)*(d3_11_3 y z w b u)))))+((((d2_6_1 y z w b u)*(d3_10_7 y z w b u))+(((d2_6_2 y z w b u)*(d3_10_6 y z w b u))+(((d2_6_3 y z w b u)*(d3_10_5 y z w b u))+((d2_6_4 y z w b u)*(d3_10_4 y z w b u)))))+((((d2_7_0 y z w b u)*(d3_9_8 y z w b u))+(((d2_7_1 y z w b u)*(d3_9_7 y z w b u))+(((d2_7_2 y z w b u)*(d3_9_6 y z w b u))+((d2_7_3 y z w b u)*(d3_9_5 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_8_8 y z w b u))+(((d2_8_1 y z w b u)*(d3_8_7 y z w b u))+((d2_8_2 y z w b u)*(d3_8_6 y z w b u))))+((((d2_9_0 y z w b u)*(d3_7_8 y z w b u))+((d2_9_1 y z w b u)*(d3_7_7 y z w b u)))+((d2_10_0 y z w b u)*(d3_6_8 y z w b u)))))))))))))+((-1)*(d4_16_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_8,d0_14_8,d0_15_7,d0_15_8,d0_16_7,d0_16_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_5,d2_10_0,d2_1_4,d2_1_5,d2_2_4,d2_2_5,d2_3_3,d2_3_4,d2_3_5,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_4,d3_10_5,d3_10_6,d3_10_7,d3_11_3,d3_11_4,d3_11_5,d3_11_6,d3_12_3,d3_12_4,d3_12_5,d3_12_6,d3_13_3,d3_13_4,d3_13_5,d3_14_3,d3_14_4,d3_15_3,d3_15_4,d3_16_3,d3_6_8,d3_7_7,d3_7_8,d3_8_6,d3_8_7,d3_8_8,d3_9_5,d3_9_6,d3_9_7,d3_9_8,d4_16_8]
  ring
#print axioms coefficient_16_8
compact_certificate_declaration theorem coefficient_16_9 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[9]?=some 0 := by
  change some (((((((d0_13_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_15_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_16_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_16_9 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_1_5 y z w b u)*(d3_15_4 y z w b u))+(((d2_2_5 y z w b u)*(d3_14_4 y z w b u))+((((d2_3_4 y z w b u)*(d3_13_5 y z w b u))+((d2_3_5 y z w b u)*(d3_13_4 y z w b u)))+((((d2_4_3 y z w b u)*(d3_12_6 y z w b u))+(((d2_4_4 y z w b u)*(d3_12_5 y z w b u))+((d2_4_5 y z w b u)*(d3_12_4 y z w b u))))+((((d2_5_3 y z w b u)*(d3_11_6 y z w b u))+(((d2_5_4 y z w b u)*(d3_11_5 y z w b u))+((d2_5_5 y z w b u)*(d3_11_4 y z w b u))))+((((d2_6_2 y z w b u)*(d3_10_7 y z w b u))+(((d2_6_3 y z w b u)*(d3_10_6 y z w b u))+((d2_6_4 y z w b u)*(d3_10_5 y z w b u))))+((((d2_7_1 y z w b u)*(d3_9_8 y z w b u))+(((d2_7_2 y z w b u)*(d3_9_7 y z w b u))+((d2_7_3 y z w b u)*(d3_9_6 y z w b u))))+((((d2_8_1 y z w b u)*(d3_8_8 y z w b u))+((d2_8_2 y z w b u)*(d3_8_7 y z w b u)))+((((d2_9_0 y z w b u)*(d3_7_9 y z w b u))+((d2_9_1 y z w b u)*(d3_7_8 y z w b u)))+((d2_10_0 y z w b u)*(d3_6_9 y z w b u))))))))))))+((-1)*(d4_16_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_9,d0_14_9,d0_15_8,d0_15_9,d0_16_8,d0_16_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_1_5,d2_2_5,d2_3_4,d2_3_5,d2_4_3,d2_4_4,d2_4_5,d2_5_3,d2_5_4,d2_5_5,d2_6_2,d2_6_3,d2_6_4,d2_7_1,d2_7_2,d2_7_3,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_5,d3_10_6,d3_10_7,d3_11_4,d3_11_5,d3_11_6,d3_12_4,d3_12_5,d3_12_6,d3_13_4,d3_13_5,d3_14_4,d3_15_4,d3_6_9,d3_7_8,d3_7_9,d3_8_7,d3_8_8,d3_9_6,d3_9_7,d3_9_8,d4_16_9]
  ring
#print axioms coefficient_16_9

compact_certificate_declaration theorem coefficient_16_10 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[10]?=some 0 := by
  change some (((((((d0_13_10 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_10 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_9 y z w b u)*(d1_1_1 y z w b u))+(((d0_15_10 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_16_9 y z w b u)*(d1_0_1 y z w b u))+(((d0_16_10 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_3_5 y z w b u)*(d3_13_5 y z w b u))+((((d2_4_4 y z w b u)*(d3_12_6 y z w b u))+((d2_4_5 y z w b u)*(d3_12_5 y z w b u)))+((((d2_5_4 y z w b u)*(d3_11_6 y z w b u))+((d2_5_5 y z w b u)*(d3_11_5 y z w b u)))+((((d2_6_3 y z w b u)*(d3_10_7 y z w b u))+((d2_6_4 y z w b u)*(d3_10_6 y z w b u)))+((((d2_7_2 y z w b u)*(d3_9_8 y z w b u))+((d2_7_3 y z w b u)*(d3_9_7 y z w b u)))+(((d2_8_2 y z w b u)*(d3_8_8 y z w b u))+((d2_9_1 y z w b u)*(d3_7_9 y z w b u)))))))))+((-1)*(d4_16_10 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_10,d0_14_10,d0_15_10,d0_15_9,d0_16_10,d0_16_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_3_5,d2_4_4,d2_4_5,d2_5_4,d2_5_5,d2_6_3,d2_6_4,d2_7_2,d2_7_3,d2_8_2,d2_9_1,d3_10_6,d3_10_7,d3_11_5,d3_11_6,d3_12_5,d3_12_6,d3_13_5,d3_7_9,d3_8_8,d3_9_7,d3_9_8,d4_16_10]
  ring
#print axioms coefficient_16_10
compact_certificate_declaration theorem coefficient_16_11 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[11]?=some 0 := by
  change some ((((((d0_13_11 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_11 y z w b u)*(d1_2_0 y z w b u))+0)+(((d0_15_10 y z w b u)*(d1_1_1 y z w b u))+((d0_16_10 y z w b u)*(d1_0_1 y z w b u)))))+(((d2_4_5 y z w b u)*(d3_12_6 y z w b u))+(((d2_5_5 y z w b u)*(d3_11_6 y z w b u))+(((d2_6_4 y z w b u)*(d3_10_7 y z w b u))+((d2_7_3 y z w b u)*(d3_9_8 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_11,d0_14_11,d0_15_10,d0_16_10,d1_0_1,d1_1_1,d1_2_0,d1_3_0,d2_4_5,d2_5_5,d2_6_4,d2_7_3,d3_10_7,d3_11_6,d3_12_6,d3_9_8]
  ring
#print axioms coefficient_16_11

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
compact_certificate_declaration theorem inner_length_17 (y z w b u : ℂ) : (innerCertificate17 y z w b u).length=12 := by
  norm_num [innerCertificate17,add,multiply,scale,inner0_14,inner0_15,inner0_16,inner0_17,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner3_7,inner3_8,inner3_9,inner4_17]
compact_certificate_declaration theorem inner_eval_17 (y z w a b u : ℂ) :
    evaluate a (innerCertificate17 y z w b u)=(((((c0_14 y z w a b u)*(c1_3 y z w a b u))+(((c0_15 y z w a b u)*(c1_2 y z w a b u))+(((c0_16 y z w a b u)*(c1_1 y z w a b u))+(((c0_17 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_17 y z w a b u))+(((c2_1 y z w a b u)*(c3_16 y z w a b u))+(((c2_2 y z w a b u)*(c3_15 y z w a b u))+(((c2_3 y z w a b u)*(c3_14 y z w a b u))+(((c2_4 y z w a b u)*(c3_13 y z w a b u))+(((c2_5 y z w a b u)*(c3_12 y z w a b u))+(((c2_6 y z w a b u)*(c3_11 y z w a b u))+(((c2_7 y z w a b u)*(c3_10 y z w a b u))+(((c2_8 y z w a b u)*(c3_9 y z w a b u))+(((c2_9 y z w a b u)*(c3_8 y z w a b u))+((c2_10 y z w a b u)*(c3_7 y z w a b u)))))))))))))+((-1)*(c4_17 y z w a b u))) := by
  simp only [innerCertificate17,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_14,c0_15,c0_16,c0_17,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_10,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_7,c3_8,c3_9,c4_17]
#print axioms inner_eval_17

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

compact_certificate_declaration theorem coefficient_17_0 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[0]?=some 0 := by
  change some (((((((d0_14_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_17_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_17_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_16_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_15_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_14_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_13_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_12_0 y z w b u))+0)+((((d2_6_0 y z w b u)*(d3_11_0 y z w b u))+0)+((((d2_7_0 y z w b u)*(d3_10_0 y z w b u))+0)+((((d2_8_0 y z w b u)*(d3_9_0 y z w b u))+0)+((((d2_9_0 y z w b u)*(d3_8_0 y z w b u))+0)+(((d2_10_0 y z w b u)*(d3_7_0 y z w b u))+0))))))))))))+(((-1)*(d4_17_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_0,d0_15_0,d0_16_0,d0_17_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_10_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d2_7_0,d2_8_0,d2_9_0,d3_10_0,d3_11_0,d3_12_0,d3_13_0,d3_14_0,d3_15_0,d3_16_0,d3_17_0,d3_7_0,d3_8_0,d3_9_0,d4_17_0]
  ring
#print axioms coefficient_17_0
compact_certificate_declaration theorem coefficient_17_1 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[1]?=some 0 := by
  change some (((((((d0_14_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_16_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_17_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_17_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_17_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_16_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_16_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_15_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_15_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_14_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_14_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_13_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_13_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_12_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_12_0 y z w b u))+0))+((((d2_6_0 y z w b u)*(d3_11_1 y z w b u))+(((d2_6_1 y z w b u)*(d3_11_0 y z w b u))+0))+((((d2_7_0 y z w b u)*(d3_10_1 y z w b u))+(((d2_7_1 y z w b u)*(d3_10_0 y z w b u))+0))+((((d2_8_0 y z w b u)*(d3_9_1 y z w b u))+(((d2_8_1 y z w b u)*(d3_9_0 y z w b u))+0))+((((d2_9_0 y z w b u)*(d3_8_1 y z w b u))+(((d2_9_1 y z w b u)*(d3_8_0 y z w b u))+0))+((d2_10_0 y z w b u)*(d3_7_1 y z w b u)))))))))))))+((-1)*(d4_17_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_1,d0_15_1,d0_16_0,d0_16_1,d0_17_0,d0_17_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_10_0,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d2_6_1,d2_7_0,d2_7_1,d2_8_0,d2_8_1,d2_9_0,d2_9_1,d3_10_0,d3_10_1,d3_11_0,d3_11_1,d3_12_0,d3_12_1,d3_13_0,d3_13_1,d3_14_0,d3_14_1,d3_15_0,d3_15_1,d3_16_0,d3_16_1,d3_17_0,d3_17_1,d3_7_1,d3_8_0,d3_8_1,d3_9_0,d3_9_1,d4_17_1]
  ring
#print axioms coefficient_17_1

compact_certificate_declaration theorem coefficient_17_2 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[2]?=some 0 := by
  change some (((((((d0_14_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_16_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_17_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_17_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_17_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_17_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_16_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_16_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_15_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_15_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_15_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_14_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_14_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_14_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_13_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_13_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_13_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_12_2 y z w b u))+(((d2_5_1 y z w b u)*(d3_12_1 y z w b u))+(((d2_5_2 y z w b u)*(d3_12_0 y z w b u))+0)))+((((d2_6_0 y z w b u)*(d3_11_2 y z w b u))+(((d2_6_1 y z w b u)*(d3_11_1 y z w b u))+(((d2_6_2 y z w b u)*(d3_11_0 y z w b u))+0)))+((((d2_7_0 y z w b u)*(d3_10_2 y z w b u))+(((d2_7_1 y z w b u)*(d3_10_1 y z w b u))+(((d2_7_2 y z w b u)*(d3_10_0 y z w b u))+0)))+((((d2_8_0 y z w b u)*(d3_9_2 y z w b u))+(((d2_8_1 y z w b u)*(d3_9_1 y z w b u))+(((d2_8_2 y z w b u)*(d3_9_0 y z w b u))+0)))+((((d2_9_0 y z w b u)*(d3_8_2 y z w b u))+((d2_9_1 y z w b u)*(d3_8_1 y z w b u)))+((d2_10_0 y z w b u)*(d3_7_2 y z w b u)))))))))))))+((-1)*(d4_17_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_2,d0_15_2,d0_16_1,d0_16_2,d0_17_1,d0_17_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_10_0,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_5_2,d2_6_0,d2_6_1,d2_6_2,d2_7_0,d2_7_1,d2_7_2,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_0,d3_10_1,d3_10_2,d3_11_0,d3_11_1,d3_11_2,d3_12_0,d3_12_1,d3_12_2,d3_13_0,d3_13_1,d3_13_2,d3_14_0,d3_14_1,d3_14_2,d3_15_0,d3_15_1,d3_15_2,d3_16_0,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d3_17_2,d3_7_2,d3_8_1,d3_8_2,d3_9_0,d3_9_1,d3_9_2,d4_17_2]
  ring
#print axioms coefficient_17_2
compact_certificate_declaration theorem coefficient_17_3 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[3]?=some 0 := by
  change some (((((((d0_14_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_16_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_17_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_17_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_17_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_17_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_16_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_16_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_16_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_15_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_15_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_15_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_15_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_14_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_14_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_14_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_14_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_13_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_13_2 y z w b u))+(((d2_4_2 y z w b u)*(d3_13_1 y z w b u))+(((d2_4_3 y z w b u)*(d3_13_0 y z w b u))+0))))+((((d2_5_0 y z w b u)*(d3_12_3 y z w b u))+(((d2_5_1 y z w b u)*(d3_12_2 y z w b u))+(((d2_5_2 y z w b u)*(d3_12_1 y z w b u))+(((d2_5_3 y z w b u)*(d3_12_0 y z w b u))+0))))+((((d2_6_0 y z w b u)*(d3_11_3 y z w b u))+(((d2_6_1 y z w b u)*(d3_11_2 y z w b u))+(((d2_6_2 y z w b u)*(d3_11_1 y z w b u))+(((d2_6_3 y z w b u)*(d3_11_0 y z w b u))+0))))+((((d2_7_0 y z w b u)*(d3_10_3 y z w b u))+(((d2_7_1 y z w b u)*(d3_10_2 y z w b u))+(((d2_7_2 y z w b u)*(d3_10_1 y z w b u))+(((d2_7_3 y z w b u)*(d3_10_0 y z w b u))+0))))+((((d2_8_0 y z w b u)*(d3_9_3 y z w b u))+(((d2_8_1 y z w b u)*(d3_9_2 y z w b u))+((d2_8_2 y z w b u)*(d3_9_1 y z w b u))))+((((d2_9_0 y z w b u)*(d3_8_3 y z w b u))+((d2_9_1 y z w b u)*(d3_8_2 y z w b u)))+((d2_10_0 y z w b u)*(d3_7_3 y z w b u)))))))))))))+((-1)*(d4_17_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_3,d0_15_3,d0_16_2,d0_16_3,d0_17_2,d0_17_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_10_0,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_0,d3_10_1,d3_10_2,d3_10_3,d3_11_0,d3_11_1,d3_11_2,d3_11_3,d3_12_0,d3_12_1,d3_12_2,d3_12_3,d3_13_0,d3_13_1,d3_13_2,d3_13_3,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_7_3,d3_8_2,d3_8_3,d3_9_1,d3_9_2,d3_9_3,d4_17_3]
  ring
#print axioms coefficient_17_3

compact_certificate_declaration theorem coefficient_17_4 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[4]?=some 0 := by
  change some (((((((d0_14_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_16_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_17_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_17_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_17_2 y z w b u))+(((d2_0_3 y z w b u)*(d3_17_1 y z w b u))+(((d2_0_4 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_1_1 y z w b u)*(d3_16_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_16_2 y z w b u))+(((d2_1_3 y z w b u)*(d3_16_1 y z w b u))+(((d2_1_4 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_15_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_15_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_15_2 y z w b u))+(((d2_2_3 y z w b u)*(d3_15_1 y z w b u))+(((d2_2_4 y z w b u)*(d3_15_0 y z w b u))+0)))))+((((d2_3_0 y z w b u)*(d3_14_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_14_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_14_2 y z w b u))+(((d2_3_3 y z w b u)*(d3_14_1 y z w b u))+(((d2_3_4 y z w b u)*(d3_14_0 y z w b u))+0)))))+((((d2_4_0 y z w b u)*(d3_13_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_13_3 y z w b u))+(((d2_4_2 y z w b u)*(d3_13_2 y z w b u))+(((d2_4_3 y z w b u)*(d3_13_1 y z w b u))+(((d2_4_4 y z w b u)*(d3_13_0 y z w b u))+0)))))+((((d2_5_0 y z w b u)*(d3_12_4 y z w b u))+(((d2_5_1 y z w b u)*(d3_12_3 y z w b u))+(((d2_5_2 y z w b u)*(d3_12_2 y z w b u))+(((d2_5_3 y z w b u)*(d3_12_1 y z w b u))+(((d2_5_4 y z w b u)*(d3_12_0 y z w b u))+0)))))+((((d2_6_0 y z w b u)*(d3_11_4 y z w b u))+(((d2_6_1 y z w b u)*(d3_11_3 y z w b u))+(((d2_6_2 y z w b u)*(d3_11_2 y z w b u))+(((d2_6_3 y z w b u)*(d3_11_1 y z w b u))+(((d2_6_4 y z w b u)*(d3_11_0 y z w b u))+0)))))+((((d2_7_0 y z w b u)*(d3_10_4 y z w b u))+(((d2_7_1 y z w b u)*(d3_10_3 y z w b u))+(((d2_7_2 y z w b u)*(d3_10_2 y z w b u))+((d2_7_3 y z w b u)*(d3_10_1 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_9_4 y z w b u))+(((d2_8_1 y z w b u)*(d3_9_3 y z w b u))+((d2_8_2 y z w b u)*(d3_9_2 y z w b u))))+((((d2_9_0 y z w b u)*(d3_8_4 y z w b u))+((d2_9_1 y z w b u)*(d3_8_3 y z w b u)))+((d2_10_0 y z w b u)*(d3_7_4 y z w b u)))))))))))))+((-1)*(d4_17_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_4,d0_15_4,d0_16_3,d0_16_4,d0_17_3,d0_17_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_0_4,d2_10_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_1,d3_10_2,d3_10_3,d3_10_4,d3_11_0,d3_11_1,d3_11_2,d3_11_3,d3_11_4,d3_12_0,d3_12_1,d3_12_2,d3_12_3,d3_12_4,d3_13_0,d3_13_1,d3_13_2,d3_13_3,d3_13_4,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_7_4,d3_8_3,d3_8_4,d3_9_2,d3_9_3,d3_9_4,d4_17_4]
  ring
#print axioms coefficient_17_4
compact_certificate_declaration theorem coefficient_17_5 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[5]?=some 0 := by
  change some (((((((d0_14_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_16_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_17_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_17_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_3 y z w b u)*(d3_17_2 y z w b u))+(((d2_0_4 y z w b u)*(d3_17_1 y z w b u))+(((d2_0_5 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_1_2 y z w b u)*(d3_16_3 y z w b u))+(((d2_1_3 y z w b u)*(d3_16_2 y z w b u))+(((d2_1_4 y z w b u)*(d3_16_1 y z w b u))+(((d2_1_5 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_2_1 y z w b u)*(d3_15_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_15_3 y z w b u))+(((d2_2_3 y z w b u)*(d3_15_2 y z w b u))+(((d2_2_4 y z w b u)*(d3_15_1 y z w b u))+(((d2_2_5 y z w b u)*(d3_15_0 y z w b u))+0)))))+((((d2_3_1 y z w b u)*(d3_14_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_14_3 y z w b u))+(((d2_3_3 y z w b u)*(d3_14_2 y z w b u))+(((d2_3_4 y z w b u)*(d3_14_1 y z w b u))+(((d2_3_5 y z w b u)*(d3_14_0 y z w b u))+0)))))+((((d2_4_0 y z w b u)*(d3_13_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_13_4 y z w b u))+(((d2_4_2 y z w b u)*(d3_13_3 y z w b u))+(((d2_4_3 y z w b u)*(d3_13_2 y z w b u))+(((d2_4_4 y z w b u)*(d3_13_1 y z w b u))+(((d2_4_5 y z w b u)*(d3_13_0 y z w b u))+0))))))+((((d2_5_0 y z w b u)*(d3_12_5 y z w b u))+(((d2_5_1 y z w b u)*(d3_12_4 y z w b u))+(((d2_5_2 y z w b u)*(d3_12_3 y z w b u))+(((d2_5_3 y z w b u)*(d3_12_2 y z w b u))+(((d2_5_4 y z w b u)*(d3_12_1 y z w b u))+(((d2_5_5 y z w b u)*(d3_12_0 y z w b u))+0))))))+((((d2_6_0 y z w b u)*(d3_11_5 y z w b u))+(((d2_6_1 y z w b u)*(d3_11_4 y z w b u))+(((d2_6_2 y z w b u)*(d3_11_3 y z w b u))+(((d2_6_3 y z w b u)*(d3_11_2 y z w b u))+((d2_6_4 y z w b u)*(d3_11_1 y z w b u))))))+((((d2_7_0 y z w b u)*(d3_10_5 y z w b u))+(((d2_7_1 y z w b u)*(d3_10_4 y z w b u))+(((d2_7_2 y z w b u)*(d3_10_3 y z w b u))+((d2_7_3 y z w b u)*(d3_10_2 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_9_5 y z w b u))+(((d2_8_1 y z w b u)*(d3_9_4 y z w b u))+((d2_8_2 y z w b u)*(d3_9_3 y z w b u))))+((((d2_9_0 y z w b u)*(d3_8_5 y z w b u))+((d2_9_1 y z w b u)*(d3_8_4 y z w b u)))+((d2_10_0 y z w b u)*(d3_7_5 y z w b u)))))))))))))+((-1)*(d4_17_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_5,d0_15_5,d0_16_4,d0_16_5,d0_17_4,d0_17_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_0_4,d2_0_5,d2_10_0,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_2,d3_10_3,d3_10_4,d3_10_5,d3_11_1,d3_11_2,d3_11_3,d3_11_4,d3_11_5,d3_12_0,d3_12_1,d3_12_2,d3_12_3,d3_12_4,d3_12_5,d3_13_0,d3_13_1,d3_13_2,d3_13_3,d3_13_4,d3_13_5,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_7_5,d3_8_4,d3_8_5,d3_9_3,d3_9_4,d3_9_5,d4_17_5]
  ring
#print axioms coefficient_17_5

compact_certificate_declaration theorem coefficient_17_6 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[6]?=some 0 := by
  change some (((((((d0_14_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_16_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_17_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_17_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_4 y z w b u)*(d3_17_2 y z w b u))+((d2_0_5 y z w b u)*(d3_17_1 y z w b u)))+((((d2_1_3 y z w b u)*(d3_16_3 y z w b u))+(((d2_1_4 y z w b u)*(d3_16_2 y z w b u))+((d2_1_5 y z w b u)*(d3_16_1 y z w b u))))+((((d2_2_2 y z w b u)*(d3_15_4 y z w b u))+(((d2_2_3 y z w b u)*(d3_15_3 y z w b u))+(((d2_2_4 y z w b u)*(d3_15_2 y z w b u))+((d2_2_5 y z w b u)*(d3_15_1 y z w b u)))))+((((d2_3_2 y z w b u)*(d3_14_4 y z w b u))+(((d2_3_3 y z w b u)*(d3_14_3 y z w b u))+(((d2_3_4 y z w b u)*(d3_14_2 y z w b u))+((d2_3_5 y z w b u)*(d3_14_1 y z w b u)))))+((((d2_4_1 y z w b u)*(d3_13_5 y z w b u))+(((d2_4_2 y z w b u)*(d3_13_4 y z w b u))+(((d2_4_3 y z w b u)*(d3_13_3 y z w b u))+(((d2_4_4 y z w b u)*(d3_13_2 y z w b u))+((d2_4_5 y z w b u)*(d3_13_1 y z w b u))))))+((((d2_5_0 y z w b u)*(d3_12_6 y z w b u))+(((d2_5_1 y z w b u)*(d3_12_5 y z w b u))+(((d2_5_2 y z w b u)*(d3_12_4 y z w b u))+(((d2_5_3 y z w b u)*(d3_12_3 y z w b u))+(((d2_5_4 y z w b u)*(d3_12_2 y z w b u))+((d2_5_5 y z w b u)*(d3_12_1 y z w b u)))))))+((((d2_6_0 y z w b u)*(d3_11_6 y z w b u))+(((d2_6_1 y z w b u)*(d3_11_5 y z w b u))+(((d2_6_2 y z w b u)*(d3_11_4 y z w b u))+(((d2_6_3 y z w b u)*(d3_11_3 y z w b u))+((d2_6_4 y z w b u)*(d3_11_2 y z w b u))))))+((((d2_7_0 y z w b u)*(d3_10_6 y z w b u))+(((d2_7_1 y z w b u)*(d3_10_5 y z w b u))+(((d2_7_2 y z w b u)*(d3_10_4 y z w b u))+((d2_7_3 y z w b u)*(d3_10_3 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_9_6 y z w b u))+(((d2_8_1 y z w b u)*(d3_9_5 y z w b u))+((d2_8_2 y z w b u)*(d3_9_4 y z w b u))))+((((d2_9_0 y z w b u)*(d3_8_6 y z w b u))+((d2_9_1 y z w b u)*(d3_8_5 y z w b u)))+((d2_10_0 y z w b u)*(d3_7_6 y z w b u)))))))))))))+((-1)*(d4_17_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_6,d0_15_6,d0_16_5,d0_16_6,d0_17_5,d0_17_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_4,d2_0_5,d2_10_0,d2_1_3,d2_1_4,d2_1_5,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_3,d3_10_4,d3_10_5,d3_10_6,d3_11_2,d3_11_3,d3_11_4,d3_11_5,d3_11_6,d3_12_1,d3_12_2,d3_12_3,d3_12_4,d3_12_5,d3_12_6,d3_13_1,d3_13_2,d3_13_3,d3_13_4,d3_13_5,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_1,d3_16_2,d3_16_3,d3_17_1,d3_17_2,d3_7_6,d3_8_5,d3_8_6,d3_9_4,d3_9_5,d3_9_6,d4_17_6]
  ring
#print axioms coefficient_17_6
compact_certificate_declaration theorem coefficient_17_7 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[7]?=some 0 := by
  change some (((((((d0_14_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_16_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_17_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_17_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_0_5 y z w b u)*(d3_17_2 y z w b u))+((((d2_1_4 y z w b u)*(d3_16_3 y z w b u))+((d2_1_5 y z w b u)*(d3_16_2 y z w b u)))+((((d2_2_3 y z w b u)*(d3_15_4 y z w b u))+(((d2_2_4 y z w b u)*(d3_15_3 y z w b u))+((d2_2_5 y z w b u)*(d3_15_2 y z w b u))))+((((d2_3_3 y z w b u)*(d3_14_4 y z w b u))+(((d2_3_4 y z w b u)*(d3_14_3 y z w b u))+((d2_3_5 y z w b u)*(d3_14_2 y z w b u))))+((((d2_4_2 y z w b u)*(d3_13_5 y z w b u))+(((d2_4_3 y z w b u)*(d3_13_4 y z w b u))+(((d2_4_4 y z w b u)*(d3_13_3 y z w b u))+((d2_4_5 y z w b u)*(d3_13_2 y z w b u)))))+((((d2_5_1 y z w b u)*(d3_12_6 y z w b u))+(((d2_5_2 y z w b u)*(d3_12_5 y z w b u))+(((d2_5_3 y z w b u)*(d3_12_4 y z w b u))+(((d2_5_4 y z w b u)*(d3_12_3 y z w b u))+((d2_5_5 y z w b u)*(d3_12_2 y z w b u))))))+((((d2_6_1 y z w b u)*(d3_11_6 y z w b u))+(((d2_6_2 y z w b u)*(d3_11_5 y z w b u))+(((d2_6_3 y z w b u)*(d3_11_4 y z w b u))+((d2_6_4 y z w b u)*(d3_11_3 y z w b u)))))+((((d2_7_0 y z w b u)*(d3_10_7 y z w b u))+(((d2_7_1 y z w b u)*(d3_10_6 y z w b u))+(((d2_7_2 y z w b u)*(d3_10_5 y z w b u))+((d2_7_3 y z w b u)*(d3_10_4 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_9_7 y z w b u))+(((d2_8_1 y z w b u)*(d3_9_6 y z w b u))+((d2_8_2 y z w b u)*(d3_9_5 y z w b u))))+((((d2_9_0 y z w b u)*(d3_8_7 y z w b u))+((d2_9_1 y z w b u)*(d3_8_6 y z w b u)))+((d2_10_0 y z w b u)*(d3_7_7 y z w b u)))))))))))))+((-1)*(d4_17_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_7,d0_15_7,d0_16_6,d0_16_7,d0_17_6,d0_17_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_5,d2_10_0,d2_1_4,d2_1_5,d2_2_3,d2_2_4,d2_2_5,d2_3_3,d2_3_4,d2_3_5,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_4,d3_10_5,d3_10_6,d3_10_7,d3_11_3,d3_11_4,d3_11_5,d3_11_6,d3_12_2,d3_12_3,d3_12_4,d3_12_5,d3_12_6,d3_13_2,d3_13_3,d3_13_4,d3_13_5,d3_14_2,d3_14_3,d3_14_4,d3_15_2,d3_15_3,d3_15_4,d3_16_2,d3_16_3,d3_17_2,d3_7_7,d3_8_6,d3_8_7,d3_9_5,d3_9_6,d3_9_7,d4_17_7]
  ring
#print axioms coefficient_17_7
compact_certificate_declaration theorem coefficient_17_8 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[8]?=some 0 := by
  change some (((((((d0_14_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_16_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_17_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_17_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_1_5 y z w b u)*(d3_16_3 y z w b u))+((((d2_2_4 y z w b u)*(d3_15_4 y z w b u))+((d2_2_5 y z w b u)*(d3_15_3 y z w b u)))+((((d2_3_4 y z w b u)*(d3_14_4 y z w b u))+((d2_3_5 y z w b u)*(d3_14_3 y z w b u)))+((((d2_4_3 y z w b u)*(d3_13_5 y z w b u))+(((d2_4_4 y z w b u)*(d3_13_4 y z w b u))+((d2_4_5 y z w b u)*(d3_13_3 y z w b u))))+((((d2_5_2 y z w b u)*(d3_12_6 y z w b u))+(((d2_5_3 y z w b u)*(d3_12_5 y z w b u))+(((d2_5_4 y z w b u)*(d3_12_4 y z w b u))+((d2_5_5 y z w b u)*(d3_12_3 y z w b u)))))+((((d2_6_2 y z w b u)*(d3_11_6 y z w b u))+(((d2_6_3 y z w b u)*(d3_11_5 y z w b u))+((d2_6_4 y z w b u)*(d3_11_4 y z w b u))))+((((d2_7_1 y z w b u)*(d3_10_7 y z w b u))+(((d2_7_2 y z w b u)*(d3_10_6 y z w b u))+((d2_7_3 y z w b u)*(d3_10_5 y z w b u))))+((((d2_8_0 y z w b u)*(d3_9_8 y z w b u))+(((d2_8_1 y z w b u)*(d3_9_7 y z w b u))+((d2_8_2 y z w b u)*(d3_9_6 y z w b u))))+((((d2_9_0 y z w b u)*(d3_8_8 y z w b u))+((d2_9_1 y z w b u)*(d3_8_7 y z w b u)))+((d2_10_0 y z w b u)*(d3_7_8 y z w b u))))))))))))+((-1)*(d4_17_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_8,d0_15_8,d0_16_7,d0_16_8,d0_17_7,d0_17_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_1_5,d2_2_4,d2_2_5,d2_3_4,d2_3_5,d2_4_3,d2_4_4,d2_4_5,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_2,d2_6_3,d2_6_4,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_5,d3_10_6,d3_10_7,d3_11_4,d3_11_5,d3_11_6,d3_12_3,d3_12_4,d3_12_5,d3_12_6,d3_13_3,d3_13_4,d3_13_5,d3_14_3,d3_14_4,d3_15_3,d3_15_4,d3_16_3,d3_7_8,d3_8_7,d3_8_8,d3_9_6,d3_9_7,d3_9_8,d4_17_8]
  ring
#print axioms coefficient_17_8

compact_certificate_declaration theorem coefficient_17_9 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[9]?=some 0 := by
  change some (((((((d0_14_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_16_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_17_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_17_9 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_2_5 y z w b u)*(d3_15_4 y z w b u))+(((d2_3_5 y z w b u)*(d3_14_4 y z w b u))+((((d2_4_4 y z w b u)*(d3_13_5 y z w b u))+((d2_4_5 y z w b u)*(d3_13_4 y z w b u)))+((((d2_5_3 y z w b u)*(d3_12_6 y z w b u))+(((d2_5_4 y z w b u)*(d3_12_5 y z w b u))+((d2_5_5 y z w b u)*(d3_12_4 y z w b u))))+((((d2_6_3 y z w b u)*(d3_11_6 y z w b u))+((d2_6_4 y z w b u)*(d3_11_5 y z w b u)))+((((d2_7_2 y z w b u)*(d3_10_7 y z w b u))+((d2_7_3 y z w b u)*(d3_10_6 y z w b u)))+((((d2_8_1 y z w b u)*(d3_9_8 y z w b u))+((d2_8_2 y z w b u)*(d3_9_7 y z w b u)))+(((d2_9_1 y z w b u)*(d3_8_8 y z w b u))+((d2_10_0 y z w b u)*(d3_7_9 y z w b u)))))))))))+((-1)*(d4_17_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_9,d0_15_9,d0_16_8,d0_16_9,d0_17_8,d0_17_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_2_5,d2_3_5,d2_4_4,d2_4_5,d2_5_3,d2_5_4,d2_5_5,d2_6_3,d2_6_4,d2_7_2,d2_7_3,d2_8_1,d2_8_2,d2_9_1,d3_10_6,d3_10_7,d3_11_5,d3_11_6,d3_12_4,d3_12_5,d3_12_6,d3_13_4,d3_13_5,d3_14_4,d3_15_4,d3_7_9,d3_8_8,d3_9_7,d3_9_8,d4_17_9]
  ring
#print axioms coefficient_17_9
compact_certificate_declaration theorem coefficient_17_10 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[10]?=some 0 := by
  change some (((((((d0_14_10 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_10 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_9 y z w b u)*(d1_1_1 y z w b u))+(((d0_16_10 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_17_9 y z w b u)*(d1_0_1 y z w b u)))))+(((d2_4_5 y z w b u)*(d3_13_5 y z w b u))+((((d2_5_4 y z w b u)*(d3_12_6 y z w b u))+((d2_5_5 y z w b u)*(d3_12_5 y z w b u)))+(((d2_6_4 y z w b u)*(d3_11_6 y z w b u))+(((d2_7_3 y z w b u)*(d3_10_7 y z w b u))+((d2_8_2 y z w b u)*(d3_9_8 y z w b u)))))))+((-1)*(d4_17_10 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_10,d0_15_10,d0_16_10,d0_16_9,d0_17_9,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_4_5,d2_5_4,d2_5_5,d2_6_4,d2_7_3,d2_8_2,d3_10_7,d3_11_6,d3_12_5,d3_12_6,d3_13_5,d3_9_8,d4_17_10]
  ring
#print axioms coefficient_17_10
compact_certificate_declaration theorem coefficient_17_11 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[11]?=some 0 := by
  change some ((((((d0_14_11 y z w b u)*(d1_3_0 y z w b u))+0)+((d0_16_10 y z w b u)*(d1_1_1 y z w b u)))+((d2_5_5 y z w b u)*(d3_12_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_11,d0_16_10,d1_1_1,d1_3_0,d2_5_5,d3_12_6]
  ring
#print axioms coefficient_17_11

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
compact_certificate_declaration theorem inner_length_18 (y z w b u : ℂ) : (innerCertificate18 y z w b u).length=11 := by
  norm_num [innerCertificate18,add,multiply,scale,inner0_15,inner0_16,inner0_17,inner0_18,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner3_18,inner3_8,inner3_9,inner4_18]
compact_certificate_declaration theorem inner_eval_18 (y z w a b u : ℂ) :
    evaluate a (innerCertificate18 y z w b u)=(((((c0_15 y z w a b u)*(c1_3 y z w a b u))+(((c0_16 y z w a b u)*(c1_2 y z w a b u))+(((c0_17 y z w a b u)*(c1_1 y z w a b u))+(((c0_18 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_18 y z w a b u))+(((c2_1 y z w a b u)*(c3_17 y z w a b u))+(((c2_2 y z w a b u)*(c3_16 y z w a b u))+(((c2_3 y z w a b u)*(c3_15 y z w a b u))+(((c2_4 y z w a b u)*(c3_14 y z w a b u))+(((c2_5 y z w a b u)*(c3_13 y z w a b u))+(((c2_6 y z w a b u)*(c3_12 y z w a b u))+(((c2_7 y z w a b u)*(c3_11 y z w a b u))+(((c2_8 y z w a b u)*(c3_10 y z w a b u))+(((c2_9 y z w a b u)*(c3_9 y z w a b u))+((c2_10 y z w a b u)*(c3_8 y z w a b u)))))))))))))+((-1)*(c4_18 y z w a b u))) := by
  simp only [innerCertificate18,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_15,c0_16,c0_17,c0_18,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_10,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_18,c3_8,c3_9,c4_18]
#print axioms inner_eval_18

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

compact_certificate_declaration theorem coefficient_18_0 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[0]?=some 0 := by
  change some (((((((d0_15_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_17_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_18_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_18_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_17_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_16_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_15_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_14_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_13_0 y z w b u))+0)+((((d2_6_0 y z w b u)*(d3_12_0 y z w b u))+0)+((((d2_7_0 y z w b u)*(d3_11_0 y z w b u))+0)+((((d2_8_0 y z w b u)*(d3_10_0 y z w b u))+0)+((((d2_9_0 y z w b u)*(d3_9_0 y z w b u))+0)+(((d2_10_0 y z w b u)*(d3_8_0 y z w b u))+0))))))))))))+(((-1)*(d4_18_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_0,d0_16_0,d0_17_0,d0_18_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_10_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d2_7_0,d2_8_0,d2_9_0,d3_10_0,d3_11_0,d3_12_0,d3_13_0,d3_14_0,d3_15_0,d3_16_0,d3_17_0,d3_18_0,d3_8_0,d3_9_0,d4_18_0]
  ring
#print axioms coefficient_18_0
compact_certificate_declaration theorem coefficient_18_1 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[1]?=some 0 := by
  change some (((((((d0_15_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_17_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_17_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_18_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_18_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_18_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_17_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_16_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_16_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_15_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_15_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_14_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_14_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_13_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_13_0 y z w b u))+0))+((((d2_6_0 y z w b u)*(d3_12_1 y z w b u))+(((d2_6_1 y z w b u)*(d3_12_0 y z w b u))+0))+((((d2_7_0 y z w b u)*(d3_11_1 y z w b u))+(((d2_7_1 y z w b u)*(d3_11_0 y z w b u))+0))+((((d2_8_0 y z w b u)*(d3_10_1 y z w b u))+(((d2_8_1 y z w b u)*(d3_10_0 y z w b u))+0))+((((d2_9_0 y z w b u)*(d3_9_1 y z w b u))+(((d2_9_1 y z w b u)*(d3_9_0 y z w b u))+0))+((d2_10_0 y z w b u)*(d3_8_1 y z w b u)))))))))))))+((-1)*(d4_18_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_1,d0_16_1,d0_17_0,d0_17_1,d0_18_0,d0_18_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_10_0,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d2_6_1,d2_7_0,d2_7_1,d2_8_0,d2_8_1,d2_9_0,d2_9_1,d3_10_0,d3_10_1,d3_11_0,d3_11_1,d3_12_0,d3_12_1,d3_13_0,d3_13_1,d3_14_0,d3_14_1,d3_15_0,d3_15_1,d3_16_0,d3_16_1,d3_17_0,d3_17_1,d3_18_0,d3_18_1,d3_8_1,d3_9_0,d3_9_1,d4_18_1]
  ring
#print axioms coefficient_18_1
compact_certificate_declaration theorem coefficient_18_2 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[2]?=some 0 := by
  change some (((((((d0_15_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_17_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_17_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_18_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_18_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_18_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_17_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_17_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_16_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_16_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_15_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_15_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_15_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_14_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_14_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_14_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_13_2 y z w b u))+(((d2_5_1 y z w b u)*(d3_13_1 y z w b u))+(((d2_5_2 y z w b u)*(d3_13_0 y z w b u))+0)))+((((d2_6_0 y z w b u)*(d3_12_2 y z w b u))+(((d2_6_1 y z w b u)*(d3_12_1 y z w b u))+(((d2_6_2 y z w b u)*(d3_12_0 y z w b u))+0)))+((((d2_7_0 y z w b u)*(d3_11_2 y z w b u))+(((d2_7_1 y z w b u)*(d3_11_1 y z w b u))+(((d2_7_2 y z w b u)*(d3_11_0 y z w b u))+0)))+((((d2_8_0 y z w b u)*(d3_10_2 y z w b u))+(((d2_8_1 y z w b u)*(d3_10_1 y z w b u))+(((d2_8_2 y z w b u)*(d3_10_0 y z w b u))+0)))+((((d2_9_0 y z w b u)*(d3_9_2 y z w b u))+((d2_9_1 y z w b u)*(d3_9_1 y z w b u)))+((d2_10_0 y z w b u)*(d3_8_2 y z w b u)))))))))))))+((-1)*(d4_18_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_2,d0_16_2,d0_17_1,d0_17_2,d0_18_1,d0_18_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_10_0,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_5_2,d2_6_0,d2_6_1,d2_6_2,d2_7_0,d2_7_1,d2_7_2,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_0,d3_10_1,d3_10_2,d3_11_0,d3_11_1,d3_11_2,d3_12_0,d3_12_1,d3_12_2,d3_13_0,d3_13_1,d3_13_2,d3_14_0,d3_14_1,d3_14_2,d3_15_0,d3_15_1,d3_15_2,d3_16_0,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_8_2,d3_9_1,d3_9_2,d4_18_2]
  ring
#print axioms coefficient_18_2

compact_certificate_declaration theorem coefficient_18_3 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[3]?=some 0 := by
  change some (((((((d0_15_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_17_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_17_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_18_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_18_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_18_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_1_1 y z w b u)*(d3_17_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_17_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_16_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_16_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_16_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_15_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_15_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_15_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_15_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_14_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_14_2 y z w b u))+(((d2_4_2 y z w b u)*(d3_14_1 y z w b u))+(((d2_4_3 y z w b u)*(d3_14_0 y z w b u))+0))))+((((d2_5_0 y z w b u)*(d3_13_3 y z w b u))+(((d2_5_1 y z w b u)*(d3_13_2 y z w b u))+(((d2_5_2 y z w b u)*(d3_13_1 y z w b u))+(((d2_5_3 y z w b u)*(d3_13_0 y z w b u))+0))))+((((d2_6_0 y z w b u)*(d3_12_3 y z w b u))+(((d2_6_1 y z w b u)*(d3_12_2 y z w b u))+(((d2_6_2 y z w b u)*(d3_12_1 y z w b u))+(((d2_6_3 y z w b u)*(d3_12_0 y z w b u))+0))))+((((d2_7_0 y z w b u)*(d3_11_3 y z w b u))+(((d2_7_1 y z w b u)*(d3_11_2 y z w b u))+(((d2_7_2 y z w b u)*(d3_11_1 y z w b u))+(((d2_7_3 y z w b u)*(d3_11_0 y z w b u))+0))))+((((d2_8_0 y z w b u)*(d3_10_3 y z w b u))+(((d2_8_1 y z w b u)*(d3_10_2 y z w b u))+((d2_8_2 y z w b u)*(d3_10_1 y z w b u))))+((((d2_9_0 y z w b u)*(d3_9_3 y z w b u))+((d2_9_1 y z w b u)*(d3_9_2 y z w b u)))+((d2_10_0 y z w b u)*(d3_8_3 y z w b u)))))))))))))+((-1)*(d4_18_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_3,d0_16_3,d0_17_2,d0_17_3,d0_18_2,d0_18_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_10_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_1,d3_10_2,d3_10_3,d3_11_0,d3_11_1,d3_11_2,d3_11_3,d3_12_0,d3_12_1,d3_12_2,d3_12_3,d3_13_0,d3_13_1,d3_13_2,d3_13_3,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_8_3,d3_9_2,d3_9_3,d4_18_3]
  ring
#print axioms coefficient_18_3
compact_certificate_declaration theorem coefficient_18_4 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[4]?=some 0 := by
  change some (((((((d0_15_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_17_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_17_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_18_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_18_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_3 y z w b u)*(d3_18_1 y z w b u))+(((d2_0_4 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_1_2 y z w b u)*(d3_17_2 y z w b u))+(((d2_1_3 y z w b u)*(d3_17_1 y z w b u))+(((d2_1_4 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_2_1 y z w b u)*(d3_16_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_16_2 y z w b u))+(((d2_2_3 y z w b u)*(d3_16_1 y z w b u))+(((d2_2_4 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_15_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_15_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_15_2 y z w b u))+(((d2_3_3 y z w b u)*(d3_15_1 y z w b u))+(((d2_3_4 y z w b u)*(d3_15_0 y z w b u))+0)))))+((((d2_4_0 y z w b u)*(d3_14_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_14_3 y z w b u))+(((d2_4_2 y z w b u)*(d3_14_2 y z w b u))+(((d2_4_3 y z w b u)*(d3_14_1 y z w b u))+(((d2_4_4 y z w b u)*(d3_14_0 y z w b u))+0)))))+((((d2_5_0 y z w b u)*(d3_13_4 y z w b u))+(((d2_5_1 y z w b u)*(d3_13_3 y z w b u))+(((d2_5_2 y z w b u)*(d3_13_2 y z w b u))+(((d2_5_3 y z w b u)*(d3_13_1 y z w b u))+(((d2_5_4 y z w b u)*(d3_13_0 y z w b u))+0)))))+((((d2_6_0 y z w b u)*(d3_12_4 y z w b u))+(((d2_6_1 y z w b u)*(d3_12_3 y z w b u))+(((d2_6_2 y z w b u)*(d3_12_2 y z w b u))+(((d2_6_3 y z w b u)*(d3_12_1 y z w b u))+(((d2_6_4 y z w b u)*(d3_12_0 y z w b u))+0)))))+((((d2_7_0 y z w b u)*(d3_11_4 y z w b u))+(((d2_7_1 y z w b u)*(d3_11_3 y z w b u))+(((d2_7_2 y z w b u)*(d3_11_2 y z w b u))+((d2_7_3 y z w b u)*(d3_11_1 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_10_4 y z w b u))+(((d2_8_1 y z w b u)*(d3_10_3 y z w b u))+((d2_8_2 y z w b u)*(d3_10_2 y z w b u))))+((((d2_9_0 y z w b u)*(d3_9_4 y z w b u))+((d2_9_1 y z w b u)*(d3_9_3 y z w b u)))+((d2_10_0 y z w b u)*(d3_8_4 y z w b u)))))))))))))+((-1)*(d4_18_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_4,d0_16_4,d0_17_3,d0_17_4,d0_18_3,d0_18_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_0_4,d2_10_0,d2_1_2,d2_1_3,d2_1_4,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_2,d3_10_3,d3_10_4,d3_11_1,d3_11_2,d3_11_3,d3_11_4,d3_12_0,d3_12_1,d3_12_2,d3_12_3,d3_12_4,d3_13_0,d3_13_1,d3_13_2,d3_13_3,d3_13_4,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_8_4,d3_9_3,d3_9_4,d4_18_4]
  ring
#print axioms coefficient_18_4

compact_certificate_declaration theorem coefficient_18_5 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[5]?=some 0 := by
  change some (((((((d0_15_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_17_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_17_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_18_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_18_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_4 y z w b u)*(d3_18_1 y z w b u))+(((d2_0_5 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_1_3 y z w b u)*(d3_17_2 y z w b u))+(((d2_1_4 y z w b u)*(d3_17_1 y z w b u))+(((d2_1_5 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_2_2 y z w b u)*(d3_16_3 y z w b u))+(((d2_2_3 y z w b u)*(d3_16_2 y z w b u))+(((d2_2_4 y z w b u)*(d3_16_1 y z w b u))+(((d2_2_5 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_3_1 y z w b u)*(d3_15_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_15_3 y z w b u))+(((d2_3_3 y z w b u)*(d3_15_2 y z w b u))+(((d2_3_4 y z w b u)*(d3_15_1 y z w b u))+(((d2_3_5 y z w b u)*(d3_15_0 y z w b u))+0)))))+((((d2_4_1 y z w b u)*(d3_14_4 y z w b u))+(((d2_4_2 y z w b u)*(d3_14_3 y z w b u))+(((d2_4_3 y z w b u)*(d3_14_2 y z w b u))+(((d2_4_4 y z w b u)*(d3_14_1 y z w b u))+(((d2_4_5 y z w b u)*(d3_14_0 y z w b u))+0)))))+((((d2_5_0 y z w b u)*(d3_13_5 y z w b u))+(((d2_5_1 y z w b u)*(d3_13_4 y z w b u))+(((d2_5_2 y z w b u)*(d3_13_3 y z w b u))+(((d2_5_3 y z w b u)*(d3_13_2 y z w b u))+(((d2_5_4 y z w b u)*(d3_13_1 y z w b u))+(((d2_5_5 y z w b u)*(d3_13_0 y z w b u))+0))))))+((((d2_6_0 y z w b u)*(d3_12_5 y z w b u))+(((d2_6_1 y z w b u)*(d3_12_4 y z w b u))+(((d2_6_2 y z w b u)*(d3_12_3 y z w b u))+(((d2_6_3 y z w b u)*(d3_12_2 y z w b u))+((d2_6_4 y z w b u)*(d3_12_1 y z w b u))))))+((((d2_7_0 y z w b u)*(d3_11_5 y z w b u))+(((d2_7_1 y z w b u)*(d3_11_4 y z w b u))+(((d2_7_2 y z w b u)*(d3_11_3 y z w b u))+((d2_7_3 y z w b u)*(d3_11_2 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_10_5 y z w b u))+(((d2_8_1 y z w b u)*(d3_10_4 y z w b u))+((d2_8_2 y z w b u)*(d3_10_3 y z w b u))))+((((d2_9_0 y z w b u)*(d3_9_5 y z w b u))+((d2_9_1 y z w b u)*(d3_9_4 y z w b u)))+((d2_10_0 y z w b u)*(d3_8_5 y z w b u)))))))))))))+((-1)*(d4_18_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_5,d0_16_5,d0_17_4,d0_17_5,d0_18_4,d0_18_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_4,d2_0_5,d2_10_0,d2_1_3,d2_1_4,d2_1_5,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_3,d3_10_4,d3_10_5,d3_11_2,d3_11_3,d3_11_4,d3_11_5,d3_12_1,d3_12_2,d3_12_3,d3_12_4,d3_12_5,d3_13_0,d3_13_1,d3_13_2,d3_13_3,d3_13_4,d3_13_5,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_8_5,d3_9_4,d3_9_5,d4_18_5]
  ring
#print axioms coefficient_18_5
compact_certificate_declaration theorem coefficient_18_6 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[6]?=some 0 := by
  change some (((((((d0_15_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_17_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_17_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_18_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_18_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_0_5 y z w b u)*(d3_18_1 y z w b u))+((((d2_1_4 y z w b u)*(d3_17_2 y z w b u))+((d2_1_5 y z w b u)*(d3_17_1 y z w b u)))+((((d2_2_3 y z w b u)*(d3_16_3 y z w b u))+(((d2_2_4 y z w b u)*(d3_16_2 y z w b u))+((d2_2_5 y z w b u)*(d3_16_1 y z w b u))))+((((d2_3_2 y z w b u)*(d3_15_4 y z w b u))+(((d2_3_3 y z w b u)*(d3_15_3 y z w b u))+(((d2_3_4 y z w b u)*(d3_15_2 y z w b u))+((d2_3_5 y z w b u)*(d3_15_1 y z w b u)))))+((((d2_4_2 y z w b u)*(d3_14_4 y z w b u))+(((d2_4_3 y z w b u)*(d3_14_3 y z w b u))+(((d2_4_4 y z w b u)*(d3_14_2 y z w b u))+((d2_4_5 y z w b u)*(d3_14_1 y z w b u)))))+((((d2_5_1 y z w b u)*(d3_13_5 y z w b u))+(((d2_5_2 y z w b u)*(d3_13_4 y z w b u))+(((d2_5_3 y z w b u)*(d3_13_3 y z w b u))+(((d2_5_4 y z w b u)*(d3_13_2 y z w b u))+((d2_5_5 y z w b u)*(d3_13_1 y z w b u))))))+((((d2_6_0 y z w b u)*(d3_12_6 y z w b u))+(((d2_6_1 y z w b u)*(d3_12_5 y z w b u))+(((d2_6_2 y z w b u)*(d3_12_4 y z w b u))+(((d2_6_3 y z w b u)*(d3_12_3 y z w b u))+((d2_6_4 y z w b u)*(d3_12_2 y z w b u))))))+((((d2_7_0 y z w b u)*(d3_11_6 y z w b u))+(((d2_7_1 y z w b u)*(d3_11_5 y z w b u))+(((d2_7_2 y z w b u)*(d3_11_4 y z w b u))+((d2_7_3 y z w b u)*(d3_11_3 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_10_6 y z w b u))+(((d2_8_1 y z w b u)*(d3_10_5 y z w b u))+((d2_8_2 y z w b u)*(d3_10_4 y z w b u))))+((((d2_9_0 y z w b u)*(d3_9_6 y z w b u))+((d2_9_1 y z w b u)*(d3_9_5 y z w b u)))+((d2_10_0 y z w b u)*(d3_8_6 y z w b u)))))))))))))+((-1)*(d4_18_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_6,d0_16_6,d0_17_5,d0_17_6,d0_18_5,d0_18_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_5,d2_10_0,d2_1_4,d2_1_5,d2_2_3,d2_2_4,d2_2_5,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_4,d3_10_5,d3_10_6,d3_11_3,d3_11_4,d3_11_5,d3_11_6,d3_12_2,d3_12_3,d3_12_4,d3_12_5,d3_12_6,d3_13_1,d3_13_2,d3_13_3,d3_13_4,d3_13_5,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_1,d3_16_2,d3_16_3,d3_17_1,d3_17_2,d3_18_1,d3_8_6,d3_9_5,d3_9_6,d4_18_6]
  ring
#print axioms coefficient_18_6
compact_certificate_declaration theorem coefficient_18_7 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[7]?=some 0 := by
  change some (((((((d0_15_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_17_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_17_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_18_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_18_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_1_5 y z w b u)*(d3_17_2 y z w b u))+((((d2_2_4 y z w b u)*(d3_16_3 y z w b u))+((d2_2_5 y z w b u)*(d3_16_2 y z w b u)))+((((d2_3_3 y z w b u)*(d3_15_4 y z w b u))+(((d2_3_4 y z w b u)*(d3_15_3 y z w b u))+((d2_3_5 y z w b u)*(d3_15_2 y z w b u))))+((((d2_4_3 y z w b u)*(d3_14_4 y z w b u))+(((d2_4_4 y z w b u)*(d3_14_3 y z w b u))+((d2_4_5 y z w b u)*(d3_14_2 y z w b u))))+((((d2_5_2 y z w b u)*(d3_13_5 y z w b u))+(((d2_5_3 y z w b u)*(d3_13_4 y z w b u))+(((d2_5_4 y z w b u)*(d3_13_3 y z w b u))+((d2_5_5 y z w b u)*(d3_13_2 y z w b u)))))+((((d2_6_1 y z w b u)*(d3_12_6 y z w b u))+(((d2_6_2 y z w b u)*(d3_12_5 y z w b u))+(((d2_6_3 y z w b u)*(d3_12_4 y z w b u))+((d2_6_4 y z w b u)*(d3_12_3 y z w b u)))))+((((d2_7_1 y z w b u)*(d3_11_6 y z w b u))+(((d2_7_2 y z w b u)*(d3_11_5 y z w b u))+((d2_7_3 y z w b u)*(d3_11_4 y z w b u))))+((((d2_8_0 y z w b u)*(d3_10_7 y z w b u))+(((d2_8_1 y z w b u)*(d3_10_6 y z w b u))+((d2_8_2 y z w b u)*(d3_10_5 y z w b u))))+((((d2_9_0 y z w b u)*(d3_9_7 y z w b u))+((d2_9_1 y z w b u)*(d3_9_6 y z w b u)))+((d2_10_0 y z w b u)*(d3_8_7 y z w b u))))))))))))+((-1)*(d4_18_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_7,d0_16_7,d0_17_6,d0_17_7,d0_18_6,d0_18_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_1_5,d2_2_4,d2_2_5,d2_3_3,d2_3_4,d2_3_5,d2_4_3,d2_4_4,d2_4_5,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_5,d3_10_6,d3_10_7,d3_11_4,d3_11_5,d3_11_6,d3_12_3,d3_12_4,d3_12_5,d3_12_6,d3_13_2,d3_13_3,d3_13_4,d3_13_5,d3_14_2,d3_14_3,d3_14_4,d3_15_2,d3_15_3,d3_15_4,d3_16_2,d3_16_3,d3_17_2,d3_8_7,d3_9_6,d3_9_7,d4_18_7]
  ring
#print axioms coefficient_18_7

compact_certificate_declaration theorem coefficient_18_8 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[8]?=some 0 := by
  change some (((((((d0_15_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_17_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_17_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_18_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_18_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_2_5 y z w b u)*(d3_16_3 y z w b u))+((((d2_3_4 y z w b u)*(d3_15_4 y z w b u))+((d2_3_5 y z w b u)*(d3_15_3 y z w b u)))+((((d2_4_4 y z w b u)*(d3_14_4 y z w b u))+((d2_4_5 y z w b u)*(d3_14_3 y z w b u)))+((((d2_5_3 y z w b u)*(d3_13_5 y z w b u))+(((d2_5_4 y z w b u)*(d3_13_4 y z w b u))+((d2_5_5 y z w b u)*(d3_13_3 y z w b u))))+((((d2_6_2 y z w b u)*(d3_12_6 y z w b u))+(((d2_6_3 y z w b u)*(d3_12_5 y z w b u))+((d2_6_4 y z w b u)*(d3_12_4 y z w b u))))+((((d2_7_2 y z w b u)*(d3_11_6 y z w b u))+((d2_7_3 y z w b u)*(d3_11_5 y z w b u)))+((((d2_8_1 y z w b u)*(d3_10_7 y z w b u))+((d2_8_2 y z w b u)*(d3_10_6 y z w b u)))+((((d2_9_0 y z w b u)*(d3_9_8 y z w b u))+((d2_9_1 y z w b u)*(d3_9_7 y z w b u)))+((d2_10_0 y z w b u)*(d3_8_8 y z w b u)))))))))))+((-1)*(d4_18_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_8,d0_16_8,d0_17_7,d0_17_8,d0_18_7,d0_18_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_2_5,d2_3_4,d2_3_5,d2_4_4,d2_4_5,d2_5_3,d2_5_4,d2_5_5,d2_6_2,d2_6_3,d2_6_4,d2_7_2,d2_7_3,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_6,d3_10_7,d3_11_5,d3_11_6,d3_12_4,d3_12_5,d3_12_6,d3_13_3,d3_13_4,d3_13_5,d3_14_3,d3_14_4,d3_15_3,d3_15_4,d3_16_3,d3_8_8,d3_9_7,d3_9_8,d4_18_8]
  ring
#print axioms coefficient_18_8
compact_certificate_declaration theorem coefficient_18_9 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[9]?=some 0 := by
  change some (((((((d0_15_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_17_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_17_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_18_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_18_9 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_3_5 y z w b u)*(d3_15_4 y z w b u))+(((d2_4_5 y z w b u)*(d3_14_4 y z w b u))+((((d2_5_4 y z w b u)*(d3_13_5 y z w b u))+((d2_5_5 y z w b u)*(d3_13_4 y z w b u)))+((((d2_6_3 y z w b u)*(d3_12_6 y z w b u))+((d2_6_4 y z w b u)*(d3_12_5 y z w b u)))+(((d2_7_3 y z w b u)*(d3_11_6 y z w b u))+(((d2_8_2 y z w b u)*(d3_10_7 y z w b u))+((d2_9_1 y z w b u)*(d3_9_8 y z w b u)))))))))+((-1)*(d4_18_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_9,d0_16_9,d0_17_8,d0_17_9,d0_18_8,d0_18_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_3_5,d2_4_5,d2_5_4,d2_5_5,d2_6_3,d2_6_4,d2_7_3,d2_8_2,d2_9_1,d3_10_7,d3_11_6,d3_12_5,d3_12_6,d3_13_4,d3_13_5,d3_14_4,d3_15_4,d3_9_8,d4_18_9]
  ring
#print axioms coefficient_18_9
compact_certificate_declaration theorem coefficient_18_10 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[10]?=some 0 := by
  change some ((((((d0_15_10 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_10 y z w b u)*(d1_2_0 y z w b u))+0)+(((d0_17_9 y z w b u)*(d1_1_1 y z w b u))+((d0_18_9 y z w b u)*(d1_0_1 y z w b u)))))+(((d2_5_5 y z w b u)*(d3_13_5 y z w b u))+((d2_6_4 y z w b u)*(d3_12_6 y z w b u)))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_10,d0_16_10,d0_17_9,d0_18_9,d1_0_1,d1_1_1,d1_2_0,d1_3_0,d2_5_5,d2_6_4,d3_12_6,d3_13_5]
  ring
#print axioms coefficient_18_10

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
compact_certificate_declaration theorem inner_length_19 (y z w b u : ℂ) : (innerCertificate19 y z w b u).length=11 := by
  norm_num [innerCertificate19,add,multiply,scale,inner0_16,inner0_17,inner0_18,inner0_19,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner3_18,inner3_19,inner3_9,inner4_19]
compact_certificate_declaration theorem inner_eval_19 (y z w a b u : ℂ) :
    evaluate a (innerCertificate19 y z w b u)=(((((c0_16 y z w a b u)*(c1_3 y z w a b u))+(((c0_17 y z w a b u)*(c1_2 y z w a b u))+(((c0_18 y z w a b u)*(c1_1 y z w a b u))+(((c0_19 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_19 y z w a b u))+(((c2_1 y z w a b u)*(c3_18 y z w a b u))+(((c2_2 y z w a b u)*(c3_17 y z w a b u))+(((c2_3 y z w a b u)*(c3_16 y z w a b u))+(((c2_4 y z w a b u)*(c3_15 y z w a b u))+(((c2_5 y z w a b u)*(c3_14 y z w a b u))+(((c2_6 y z w a b u)*(c3_13 y z w a b u))+(((c2_7 y z w a b u)*(c3_12 y z w a b u))+(((c2_8 y z w a b u)*(c3_11 y z w a b u))+(((c2_9 y z w a b u)*(c3_10 y z w a b u))+((c2_10 y z w a b u)*(c3_9 y z w a b u)))))))))))))+((-1)*(c4_19 y z w a b u))) := by
  simp only [innerCertificate19,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_16,c0_17,c0_18,c0_19,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_10,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_18,c3_19,c3_9,c4_19]
#print axioms inner_eval_19

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

compact_certificate_declaration theorem coefficient_19_0 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[0]?=some 0 := by
  change some (((((((d0_16_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_17_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_18_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_19_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_18_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_17_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_16_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_15_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_14_0 y z w b u))+0)+((((d2_6_0 y z w b u)*(d3_13_0 y z w b u))+0)+((((d2_7_0 y z w b u)*(d3_12_0 y z w b u))+0)+((((d2_8_0 y z w b u)*(d3_11_0 y z w b u))+0)+((((d2_9_0 y z w b u)*(d3_10_0 y z w b u))+0)+(((d2_10_0 y z w b u)*(d3_9_0 y z w b u))+0))))))))))))+(((-1)*(d4_19_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_0,d0_17_0,d0_18_0,d0_19_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_10_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d2_7_0,d2_8_0,d2_9_0,d3_10_0,d3_11_0,d3_12_0,d3_13_0,d3_14_0,d3_15_0,d3_16_0,d3_17_0,d3_18_0,d3_19_0,d3_9_0,d4_19_0]
  ring
#print axioms coefficient_19_0
compact_certificate_declaration theorem coefficient_19_1 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[1]?=some 0 := by
  change some (((((((d0_16_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_17_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_18_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_18_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_19_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_19_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_18_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_17_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_16_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_16_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_15_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_15_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_14_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_14_0 y z w b u))+0))+((((d2_6_0 y z w b u)*(d3_13_1 y z w b u))+(((d2_6_1 y z w b u)*(d3_13_0 y z w b u))+0))+((((d2_7_0 y z w b u)*(d3_12_1 y z w b u))+(((d2_7_1 y z w b u)*(d3_12_0 y z w b u))+0))+((((d2_8_0 y z w b u)*(d3_11_1 y z w b u))+(((d2_8_1 y z w b u)*(d3_11_0 y z w b u))+0))+((((d2_9_0 y z w b u)*(d3_10_1 y z w b u))+(((d2_9_1 y z w b u)*(d3_10_0 y z w b u))+0))+((d2_10_0 y z w b u)*(d3_9_1 y z w b u)))))))))))))+((-1)*(d4_19_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_1,d0_17_1,d0_18_0,d0_18_1,d0_19_0,d0_19_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_10_0,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d2_6_1,d2_7_0,d2_7_1,d2_8_0,d2_8_1,d2_9_0,d2_9_1,d3_10_0,d3_10_1,d3_11_0,d3_11_1,d3_12_0,d3_12_1,d3_13_0,d3_13_1,d3_14_0,d3_14_1,d3_15_0,d3_15_1,d3_16_0,d3_16_1,d3_17_0,d3_17_1,d3_18_0,d3_18_1,d3_19_0,d3_9_1,d4_19_1]
  ring
#print axioms coefficient_19_1
compact_certificate_declaration theorem coefficient_19_2 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[2]?=some 0 := by
  change some (((((((d0_16_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_17_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_18_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_18_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_19_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_19_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_1_1 y z w b u)*(d3_18_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_17_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_17_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_16_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_16_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_15_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_15_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_15_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_14_2 y z w b u))+(((d2_5_1 y z w b u)*(d3_14_1 y z w b u))+(((d2_5_2 y z w b u)*(d3_14_0 y z w b u))+0)))+((((d2_6_0 y z w b u)*(d3_13_2 y z w b u))+(((d2_6_1 y z w b u)*(d3_13_1 y z w b u))+(((d2_6_2 y z w b u)*(d3_13_0 y z w b u))+0)))+((((d2_7_0 y z w b u)*(d3_12_2 y z w b u))+(((d2_7_1 y z w b u)*(d3_12_1 y z w b u))+(((d2_7_2 y z w b u)*(d3_12_0 y z w b u))+0)))+((((d2_8_0 y z w b u)*(d3_11_2 y z w b u))+(((d2_8_1 y z w b u)*(d3_11_1 y z w b u))+(((d2_8_2 y z w b u)*(d3_11_0 y z w b u))+0)))+((((d2_9_0 y z w b u)*(d3_10_2 y z w b u))+((d2_9_1 y z w b u)*(d3_10_1 y z w b u)))+((d2_10_0 y z w b u)*(d3_9_2 y z w b u)))))))))))))+((-1)*(d4_19_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_2,d0_17_2,d0_18_1,d0_18_2,d0_19_1,d0_19_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_10_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_5_2,d2_6_0,d2_6_1,d2_6_2,d2_7_0,d2_7_1,d2_7_2,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_1,d3_10_2,d3_11_0,d3_11_1,d3_11_2,d3_12_0,d3_12_1,d3_12_2,d3_13_0,d3_13_1,d3_13_2,d3_14_0,d3_14_1,d3_14_2,d3_15_0,d3_15_1,d3_15_2,d3_16_0,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d3_9_2,d4_19_2]
  ring
#print axioms coefficient_19_2

compact_certificate_declaration theorem coefficient_19_3 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[3]?=some 0 := by
  change some (((((((d0_16_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_17_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_18_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_18_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_19_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_19_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_3 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_1_2 y z w b u)*(d3_18_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_2_1 y z w b u)*(d3_17_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_17_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_16_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_16_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_16_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_15_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_15_2 y z w b u))+(((d2_4_2 y z w b u)*(d3_15_1 y z w b u))+(((d2_4_3 y z w b u)*(d3_15_0 y z w b u))+0))))+((((d2_5_0 y z w b u)*(d3_14_3 y z w b u))+(((d2_5_1 y z w b u)*(d3_14_2 y z w b u))+(((d2_5_2 y z w b u)*(d3_14_1 y z w b u))+(((d2_5_3 y z w b u)*(d3_14_0 y z w b u))+0))))+((((d2_6_0 y z w b u)*(d3_13_3 y z w b u))+(((d2_6_1 y z w b u)*(d3_13_2 y z w b u))+(((d2_6_2 y z w b u)*(d3_13_1 y z w b u))+(((d2_6_3 y z w b u)*(d3_13_0 y z w b u))+0))))+((((d2_7_0 y z w b u)*(d3_12_3 y z w b u))+(((d2_7_1 y z w b u)*(d3_12_2 y z w b u))+(((d2_7_2 y z w b u)*(d3_12_1 y z w b u))+(((d2_7_3 y z w b u)*(d3_12_0 y z w b u))+0))))+((((d2_8_0 y z w b u)*(d3_11_3 y z w b u))+(((d2_8_1 y z w b u)*(d3_11_2 y z w b u))+((d2_8_2 y z w b u)*(d3_11_1 y z w b u))))+((((d2_9_0 y z w b u)*(d3_10_3 y z w b u))+((d2_9_1 y z w b u)*(d3_10_2 y z w b u)))+((d2_10_0 y z w b u)*(d3_9_3 y z w b u)))))))))))))+((-1)*(d4_19_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_3,d0_17_3,d0_18_2,d0_18_3,d0_19_2,d0_19_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_10_0,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_2,d3_10_3,d3_11_1,d3_11_2,d3_11_3,d3_12_0,d3_12_1,d3_12_2,d3_12_3,d3_13_0,d3_13_1,d3_13_2,d3_13_3,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d3_9_3,d4_19_3]
  ring
#print axioms coefficient_19_3
compact_certificate_declaration theorem coefficient_19_4 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[4]?=some 0 := by
  change some (((((((d0_16_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_17_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_18_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_18_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_19_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_19_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_4 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_1_3 y z w b u)*(d3_18_1 y z w b u))+(((d2_1_4 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_2_2 y z w b u)*(d3_17_2 y z w b u))+(((d2_2_3 y z w b u)*(d3_17_1 y z w b u))+(((d2_2_4 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_3_1 y z w b u)*(d3_16_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_16_2 y z w b u))+(((d2_3_3 y z w b u)*(d3_16_1 y z w b u))+(((d2_3_4 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_15_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_15_3 y z w b u))+(((d2_4_2 y z w b u)*(d3_15_2 y z w b u))+(((d2_4_3 y z w b u)*(d3_15_1 y z w b u))+(((d2_4_4 y z w b u)*(d3_15_0 y z w b u))+0)))))+((((d2_5_0 y z w b u)*(d3_14_4 y z w b u))+(((d2_5_1 y z w b u)*(d3_14_3 y z w b u))+(((d2_5_2 y z w b u)*(d3_14_2 y z w b u))+(((d2_5_3 y z w b u)*(d3_14_1 y z w b u))+(((d2_5_4 y z w b u)*(d3_14_0 y z w b u))+0)))))+((((d2_6_0 y z w b u)*(d3_13_4 y z w b u))+(((d2_6_1 y z w b u)*(d3_13_3 y z w b u))+(((d2_6_2 y z w b u)*(d3_13_2 y z w b u))+(((d2_6_3 y z w b u)*(d3_13_1 y z w b u))+(((d2_6_4 y z w b u)*(d3_13_0 y z w b u))+0)))))+((((d2_7_0 y z w b u)*(d3_12_4 y z w b u))+(((d2_7_1 y z w b u)*(d3_12_3 y z w b u))+(((d2_7_2 y z w b u)*(d3_12_2 y z w b u))+((d2_7_3 y z w b u)*(d3_12_1 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_11_4 y z w b u))+(((d2_8_1 y z w b u)*(d3_11_3 y z w b u))+((d2_8_2 y z w b u)*(d3_11_2 y z w b u))))+((((d2_9_0 y z w b u)*(d3_10_4 y z w b u))+((d2_9_1 y z w b u)*(d3_10_3 y z w b u)))+((d2_10_0 y z w b u)*(d3_9_4 y z w b u)))))))))))))+((-1)*(d4_19_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_4,d0_17_4,d0_18_3,d0_18_4,d0_19_3,d0_19_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_4,d2_10_0,d2_1_3,d2_1_4,d2_2_2,d2_2_3,d2_2_4,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_3,d3_10_4,d3_11_2,d3_11_3,d3_11_4,d3_12_1,d3_12_2,d3_12_3,d3_12_4,d3_13_0,d3_13_1,d3_13_2,d3_13_3,d3_13_4,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d3_9_4,d4_19_4]
  ring
#print axioms coefficient_19_4
compact_certificate_declaration theorem coefficient_19_5 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[5]?=some 0 := by
  change some (((((((d0_16_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_17_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_18_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_18_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_19_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_19_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_5 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_1_4 y z w b u)*(d3_18_1 y z w b u))+(((d2_1_5 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_2_3 y z w b u)*(d3_17_2 y z w b u))+(((d2_2_4 y z w b u)*(d3_17_1 y z w b u))+(((d2_2_5 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_3_2 y z w b u)*(d3_16_3 y z w b u))+(((d2_3_3 y z w b u)*(d3_16_2 y z w b u))+(((d2_3_4 y z w b u)*(d3_16_1 y z w b u))+(((d2_3_5 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_4_1 y z w b u)*(d3_15_4 y z w b u))+(((d2_4_2 y z w b u)*(d3_15_3 y z w b u))+(((d2_4_3 y z w b u)*(d3_15_2 y z w b u))+(((d2_4_4 y z w b u)*(d3_15_1 y z w b u))+(((d2_4_5 y z w b u)*(d3_15_0 y z w b u))+0)))))+((((d2_5_1 y z w b u)*(d3_14_4 y z w b u))+(((d2_5_2 y z w b u)*(d3_14_3 y z w b u))+(((d2_5_3 y z w b u)*(d3_14_2 y z w b u))+(((d2_5_4 y z w b u)*(d3_14_1 y z w b u))+(((d2_5_5 y z w b u)*(d3_14_0 y z w b u))+0)))))+((((d2_6_0 y z w b u)*(d3_13_5 y z w b u))+(((d2_6_1 y z w b u)*(d3_13_4 y z w b u))+(((d2_6_2 y z w b u)*(d3_13_3 y z w b u))+(((d2_6_3 y z w b u)*(d3_13_2 y z w b u))+((d2_6_4 y z w b u)*(d3_13_1 y z w b u))))))+((((d2_7_0 y z w b u)*(d3_12_5 y z w b u))+(((d2_7_1 y z w b u)*(d3_12_4 y z w b u))+(((d2_7_2 y z w b u)*(d3_12_3 y z w b u))+((d2_7_3 y z w b u)*(d3_12_2 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_11_5 y z w b u))+(((d2_8_1 y z w b u)*(d3_11_4 y z w b u))+((d2_8_2 y z w b u)*(d3_11_3 y z w b u))))+((((d2_9_0 y z w b u)*(d3_10_5 y z w b u))+((d2_9_1 y z w b u)*(d3_10_4 y z w b u)))+((d2_10_0 y z w b u)*(d3_9_5 y z w b u)))))))))))))+((-1)*(d4_19_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_5,d0_17_5,d0_18_4,d0_18_5,d0_19_4,d0_19_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_5,d2_10_0,d2_1_4,d2_1_5,d2_2_3,d2_2_4,d2_2_5,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_4,d3_10_5,d3_11_3,d3_11_4,d3_11_5,d3_12_2,d3_12_3,d3_12_4,d3_12_5,d3_13_1,d3_13_2,d3_13_3,d3_13_4,d3_13_5,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d3_9_5,d4_19_5]
  ring
#print axioms coefficient_19_5

compact_certificate_declaration theorem coefficient_19_6 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[6]?=some 0 := by
  change some (((((((d0_16_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_17_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_18_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_18_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_19_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_19_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_1_5 y z w b u)*(d3_18_1 y z w b u))+((((d2_2_4 y z w b u)*(d3_17_2 y z w b u))+((d2_2_5 y z w b u)*(d3_17_1 y z w b u)))+((((d2_3_3 y z w b u)*(d3_16_3 y z w b u))+(((d2_3_4 y z w b u)*(d3_16_2 y z w b u))+((d2_3_5 y z w b u)*(d3_16_1 y z w b u))))+((((d2_4_2 y z w b u)*(d3_15_4 y z w b u))+(((d2_4_3 y z w b u)*(d3_15_3 y z w b u))+(((d2_4_4 y z w b u)*(d3_15_2 y z w b u))+((d2_4_5 y z w b u)*(d3_15_1 y z w b u)))))+((((d2_5_2 y z w b u)*(d3_14_4 y z w b u))+(((d2_5_3 y z w b u)*(d3_14_3 y z w b u))+(((d2_5_4 y z w b u)*(d3_14_2 y z w b u))+((d2_5_5 y z w b u)*(d3_14_1 y z w b u)))))+((((d2_6_1 y z w b u)*(d3_13_5 y z w b u))+(((d2_6_2 y z w b u)*(d3_13_4 y z w b u))+(((d2_6_3 y z w b u)*(d3_13_3 y z w b u))+((d2_6_4 y z w b u)*(d3_13_2 y z w b u)))))+((((d2_7_0 y z w b u)*(d3_12_6 y z w b u))+(((d2_7_1 y z w b u)*(d3_12_5 y z w b u))+(((d2_7_2 y z w b u)*(d3_12_4 y z w b u))+((d2_7_3 y z w b u)*(d3_12_3 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_11_6 y z w b u))+(((d2_8_1 y z w b u)*(d3_11_5 y z w b u))+((d2_8_2 y z w b u)*(d3_11_4 y z w b u))))+((((d2_9_0 y z w b u)*(d3_10_6 y z w b u))+((d2_9_1 y z w b u)*(d3_10_5 y z w b u)))+((d2_10_0 y z w b u)*(d3_9_6 y z w b u))))))))))))+((-1)*(d4_19_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_6,d0_17_6,d0_18_5,d0_18_6,d0_19_5,d0_19_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_1_5,d2_2_4,d2_2_5,d2_3_3,d2_3_4,d2_3_5,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_5,d3_10_6,d3_11_4,d3_11_5,d3_11_6,d3_12_3,d3_12_4,d3_12_5,d3_12_6,d3_13_2,d3_13_3,d3_13_4,d3_13_5,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_1,d3_16_2,d3_16_3,d3_17_1,d3_17_2,d3_18_1,d3_9_6,d4_19_6]
  ring
#print axioms coefficient_19_6
compact_certificate_declaration theorem coefficient_19_7 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[7]?=some 0 := by
  change some (((((((d0_16_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_17_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_18_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_18_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_19_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_19_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_2_5 y z w b u)*(d3_17_2 y z w b u))+((((d2_3_4 y z w b u)*(d3_16_3 y z w b u))+((d2_3_5 y z w b u)*(d3_16_2 y z w b u)))+((((d2_4_3 y z w b u)*(d3_15_4 y z w b u))+(((d2_4_4 y z w b u)*(d3_15_3 y z w b u))+((d2_4_5 y z w b u)*(d3_15_2 y z w b u))))+((((d2_5_3 y z w b u)*(d3_14_4 y z w b u))+(((d2_5_4 y z w b u)*(d3_14_3 y z w b u))+((d2_5_5 y z w b u)*(d3_14_2 y z w b u))))+((((d2_6_2 y z w b u)*(d3_13_5 y z w b u))+(((d2_6_3 y z w b u)*(d3_13_4 y z w b u))+((d2_6_4 y z w b u)*(d3_13_3 y z w b u))))+((((d2_7_1 y z w b u)*(d3_12_6 y z w b u))+(((d2_7_2 y z w b u)*(d3_12_5 y z w b u))+((d2_7_3 y z w b u)*(d3_12_4 y z w b u))))+((((d2_8_1 y z w b u)*(d3_11_6 y z w b u))+((d2_8_2 y z w b u)*(d3_11_5 y z w b u)))+((((d2_9_0 y z w b u)*(d3_10_7 y z w b u))+((d2_9_1 y z w b u)*(d3_10_6 y z w b u)))+((d2_10_0 y z w b u)*(d3_9_7 y z w b u)))))))))))+((-1)*(d4_19_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_7,d0_17_7,d0_18_6,d0_18_7,d0_19_6,d0_19_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_2_5,d2_3_4,d2_3_5,d2_4_3,d2_4_4,d2_4_5,d2_5_3,d2_5_4,d2_5_5,d2_6_2,d2_6_3,d2_6_4,d2_7_1,d2_7_2,d2_7_3,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_6,d3_10_7,d3_11_5,d3_11_6,d3_12_4,d3_12_5,d3_12_6,d3_13_3,d3_13_4,d3_13_5,d3_14_2,d3_14_3,d3_14_4,d3_15_2,d3_15_3,d3_15_4,d3_16_2,d3_16_3,d3_17_2,d3_9_7,d4_19_7]
  ring
#print axioms coefficient_19_7
compact_certificate_declaration theorem coefficient_19_8 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[8]?=some 0 := by
  change some (((((((d0_16_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_17_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_18_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_18_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_19_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_19_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_3_5 y z w b u)*(d3_16_3 y z w b u))+((((d2_4_4 y z w b u)*(d3_15_4 y z w b u))+((d2_4_5 y z w b u)*(d3_15_3 y z w b u)))+((((d2_5_4 y z w b u)*(d3_14_4 y z w b u))+((d2_5_5 y z w b u)*(d3_14_3 y z w b u)))+((((d2_6_3 y z w b u)*(d3_13_5 y z w b u))+((d2_6_4 y z w b u)*(d3_13_4 y z w b u)))+((((d2_7_2 y z w b u)*(d3_12_6 y z w b u))+((d2_7_3 y z w b u)*(d3_12_5 y z w b u)))+(((d2_8_2 y z w b u)*(d3_11_6 y z w b u))+(((d2_9_1 y z w b u)*(d3_10_7 y z w b u))+((d2_10_0 y z w b u)*(d3_9_8 y z w b u))))))))))+((-1)*(d4_19_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_8,d0_17_8,d0_18_7,d0_18_8,d0_19_7,d0_19_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_3_5,d2_4_4,d2_4_5,d2_5_4,d2_5_5,d2_6_3,d2_6_4,d2_7_2,d2_7_3,d2_8_2,d2_9_1,d3_10_7,d3_11_6,d3_12_5,d3_12_6,d3_13_4,d3_13_5,d3_14_3,d3_14_4,d3_15_3,d3_15_4,d3_16_3,d3_9_8,d4_19_8]
  ring
#print axioms coefficient_19_8

compact_certificate_declaration theorem coefficient_19_9 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[9]?=some 0 := by
  change some (((((((d0_16_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_17_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_18_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_18_9 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_19_8 y z w b u)*(d1_0_1 y z w b u)))))+(((d2_4_5 y z w b u)*(d3_15_4 y z w b u))+(((d2_5_5 y z w b u)*(d3_14_4 y z w b u))+(((d2_6_4 y z w b u)*(d3_13_5 y z w b u))+((d2_7_3 y z w b u)*(d3_12_6 y z w b u))))))+((-1)*(d4_19_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_9,d0_17_9,d0_18_8,d0_18_9,d0_19_8,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_4_5,d2_5_5,d2_6_4,d2_7_3,d3_12_6,d3_13_5,d3_14_4,d3_15_4,d4_19_9]
  ring
#print axioms coefficient_19_9
compact_certificate_declaration theorem coefficient_19_10 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[10]?=some 0 := by
  change some (((((d0_16_10 y z w b u)*(d1_3_0 y z w b u))+0)+((d0_18_9 y z w b u)*(d1_1_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_10,d0_18_9,d1_1_1,d1_3_0]
  ring
#print axioms coefficient_19_10

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
compact_certificate_declaration theorem inner_length_20 (y z w b u : ℂ) : (innerCertificate20 y z w b u).length=10 := by
  norm_num [innerCertificate20,add,multiply,scale,inner0_17,inner0_18,inner0_19,inner0_20,inner1_0,inner1_1,inner1_2,inner1_3,inner2_1,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner3_18,inner3_19,inner4_20]
compact_certificate_declaration theorem inner_eval_20 (y z w a b u : ℂ) :
    evaluate a (innerCertificate20 y z w b u)=(((((c0_17 y z w a b u)*(c1_3 y z w a b u))+(((c0_18 y z w a b u)*(c1_2 y z w a b u))+(((c0_19 y z w a b u)*(c1_1 y z w a b u))+(((c0_20 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_1 y z w a b u)*(c3_19 y z w a b u))+(((c2_2 y z w a b u)*(c3_18 y z w a b u))+(((c2_3 y z w a b u)*(c3_17 y z w a b u))+(((c2_4 y z w a b u)*(c3_16 y z w a b u))+(((c2_5 y z w a b u)*(c3_15 y z w a b u))+(((c2_6 y z w a b u)*(c3_14 y z w a b u))+(((c2_7 y z w a b u)*(c3_13 y z w a b u))+(((c2_8 y z w a b u)*(c3_12 y z w a b u))+(((c2_9 y z w a b u)*(c3_11 y z w a b u))+((c2_10 y z w a b u)*(c3_10 y z w a b u))))))))))))+((-1)*(c4_20 y z w a b u))) := by
  simp only [innerCertificate20,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_17,c0_18,c0_19,c0_20,c1_0,c1_1,c1_2,c1_3,c2_1,c2_10,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_18,c3_19,c4_20]
#print axioms inner_eval_20

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

compact_certificate_declaration theorem coefficient_20_0 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[0]?=some 0 := by
  change some (((((((d0_17_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_18_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_19_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_20_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_18_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_17_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_16_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_15_0 y z w b u))+0)+((((d2_6_0 y z w b u)*(d3_14_0 y z w b u))+0)+((((d2_7_0 y z w b u)*(d3_13_0 y z w b u))+0)+((((d2_8_0 y z w b u)*(d3_12_0 y z w b u))+0)+((((d2_9_0 y z w b u)*(d3_11_0 y z w b u))+0)+(((d2_10_0 y z w b u)*(d3_10_0 y z w b u))+0)))))))))))+(((-1)*(d4_20_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_17_0,d0_18_0,d0_19_0,d0_20_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_10_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d2_7_0,d2_8_0,d2_9_0,d3_10_0,d3_11_0,d3_12_0,d3_13_0,d3_14_0,d3_15_0,d3_16_0,d3_17_0,d3_18_0,d3_19_0,d4_20_0]
  ring
#print axioms coefficient_20_0
compact_certificate_declaration theorem coefficient_20_1 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[1]?=some 0 := by
  change some (((((((d0_17_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_18_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_19_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_19_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_20_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_20_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_1_1 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_18_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_17_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_16_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_16_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_15_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_15_0 y z w b u))+0))+((((d2_6_0 y z w b u)*(d3_14_1 y z w b u))+(((d2_6_1 y z w b u)*(d3_14_0 y z w b u))+0))+((((d2_7_0 y z w b u)*(d3_13_1 y z w b u))+(((d2_7_1 y z w b u)*(d3_13_0 y z w b u))+0))+((((d2_8_0 y z w b u)*(d3_12_1 y z w b u))+(((d2_8_1 y z w b u)*(d3_12_0 y z w b u))+0))+((((d2_9_0 y z w b u)*(d3_11_1 y z w b u))+(((d2_9_1 y z w b u)*(d3_11_0 y z w b u))+0))+((d2_10_0 y z w b u)*(d3_10_1 y z w b u))))))))))))+((-1)*(d4_20_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_17_1,d0_18_1,d0_19_0,d0_19_1,d0_20_0,d0_20_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d2_6_1,d2_7_0,d2_7_1,d2_8_0,d2_8_1,d2_9_0,d2_9_1,d3_10_1,d3_11_0,d3_11_1,d3_12_0,d3_12_1,d3_13_0,d3_13_1,d3_14_0,d3_14_1,d3_15_0,d3_15_1,d3_16_0,d3_16_1,d3_17_0,d3_17_1,d3_18_0,d3_18_1,d3_19_0,d4_20_1]
  ring
#print axioms coefficient_20_1
compact_certificate_declaration theorem coefficient_20_2 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[2]?=some 0 := by
  change some (((((((d0_17_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_18_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_19_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_19_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_20_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_20_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_1_2 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_2_1 y z w b u)*(d3_18_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_17_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_17_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_16_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_16_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_15_2 y z w b u))+(((d2_5_1 y z w b u)*(d3_15_1 y z w b u))+(((d2_5_2 y z w b u)*(d3_15_0 y z w b u))+0)))+((((d2_6_0 y z w b u)*(d3_14_2 y z w b u))+(((d2_6_1 y z w b u)*(d3_14_1 y z w b u))+(((d2_6_2 y z w b u)*(d3_14_0 y z w b u))+0)))+((((d2_7_0 y z w b u)*(d3_13_2 y z w b u))+(((d2_7_1 y z w b u)*(d3_13_1 y z w b u))+(((d2_7_2 y z w b u)*(d3_13_0 y z w b u))+0)))+((((d2_8_0 y z w b u)*(d3_12_2 y z w b u))+(((d2_8_1 y z w b u)*(d3_12_1 y z w b u))+(((d2_8_2 y z w b u)*(d3_12_0 y z w b u))+0)))+((((d2_9_0 y z w b u)*(d3_11_2 y z w b u))+((d2_9_1 y z w b u)*(d3_11_1 y z w b u)))+((d2_10_0 y z w b u)*(d3_10_2 y z w b u))))))))))))+((-1)*(d4_20_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_17_2,d0_18_2,d0_19_1,d0_19_2,d0_20_1,d0_20_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_1_2,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_5_2,d2_6_0,d2_6_1,d2_6_2,d2_7_0,d2_7_1,d2_7_2,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_2,d3_11_1,d3_11_2,d3_12_0,d3_12_1,d3_12_2,d3_13_0,d3_13_1,d3_13_2,d3_14_0,d3_14_1,d3_14_2,d3_15_0,d3_15_1,d3_15_2,d3_16_0,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_20_2]
  ring
#print axioms coefficient_20_2

compact_certificate_declaration theorem coefficient_20_3 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[3]?=some 0 := by
  change some (((((((d0_17_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_18_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_19_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_19_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_20_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_20_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_1_3 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_2_2 y z w b u)*(d3_18_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_3_1 y z w b u)*(d3_17_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_17_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_16_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_16_2 y z w b u))+(((d2_4_2 y z w b u)*(d3_16_1 y z w b u))+(((d2_4_3 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_5_0 y z w b u)*(d3_15_3 y z w b u))+(((d2_5_1 y z w b u)*(d3_15_2 y z w b u))+(((d2_5_2 y z w b u)*(d3_15_1 y z w b u))+(((d2_5_3 y z w b u)*(d3_15_0 y z w b u))+0))))+((((d2_6_0 y z w b u)*(d3_14_3 y z w b u))+(((d2_6_1 y z w b u)*(d3_14_2 y z w b u))+(((d2_6_2 y z w b u)*(d3_14_1 y z w b u))+(((d2_6_3 y z w b u)*(d3_14_0 y z w b u))+0))))+((((d2_7_0 y z w b u)*(d3_13_3 y z w b u))+(((d2_7_1 y z w b u)*(d3_13_2 y z w b u))+(((d2_7_2 y z w b u)*(d3_13_1 y z w b u))+(((d2_7_3 y z w b u)*(d3_13_0 y z w b u))+0))))+((((d2_8_0 y z w b u)*(d3_12_3 y z w b u))+(((d2_8_1 y z w b u)*(d3_12_2 y z w b u))+((d2_8_2 y z w b u)*(d3_12_1 y z w b u))))+((((d2_9_0 y z w b u)*(d3_11_3 y z w b u))+((d2_9_1 y z w b u)*(d3_11_2 y z w b u)))+((d2_10_0 y z w b u)*(d3_10_3 y z w b u))))))))))))+((-1)*(d4_20_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_17_3,d0_18_3,d0_19_2,d0_19_3,d0_20_2,d0_20_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_1_3,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_3,d3_11_2,d3_11_3,d3_12_1,d3_12_2,d3_12_3,d3_13_0,d3_13_1,d3_13_2,d3_13_3,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_20_3]
  ring
#print axioms coefficient_20_3
compact_certificate_declaration theorem coefficient_20_4 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[4]?=some 0 := by
  change some (((((((d0_17_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_18_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_19_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_19_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_20_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_20_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_1_4 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_2_3 y z w b u)*(d3_18_1 y z w b u))+(((d2_2_4 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_3_2 y z w b u)*(d3_17_2 y z w b u))+(((d2_3_3 y z w b u)*(d3_17_1 y z w b u))+(((d2_3_4 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_4_1 y z w b u)*(d3_16_3 y z w b u))+(((d2_4_2 y z w b u)*(d3_16_2 y z w b u))+(((d2_4_3 y z w b u)*(d3_16_1 y z w b u))+(((d2_4_4 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_5_0 y z w b u)*(d3_15_4 y z w b u))+(((d2_5_1 y z w b u)*(d3_15_3 y z w b u))+(((d2_5_2 y z w b u)*(d3_15_2 y z w b u))+(((d2_5_3 y z w b u)*(d3_15_1 y z w b u))+(((d2_5_4 y z w b u)*(d3_15_0 y z w b u))+0)))))+((((d2_6_0 y z w b u)*(d3_14_4 y z w b u))+(((d2_6_1 y z w b u)*(d3_14_3 y z w b u))+(((d2_6_2 y z w b u)*(d3_14_2 y z w b u))+(((d2_6_3 y z w b u)*(d3_14_1 y z w b u))+(((d2_6_4 y z w b u)*(d3_14_0 y z w b u))+0)))))+((((d2_7_0 y z w b u)*(d3_13_4 y z w b u))+(((d2_7_1 y z w b u)*(d3_13_3 y z w b u))+(((d2_7_2 y z w b u)*(d3_13_2 y z w b u))+((d2_7_3 y z w b u)*(d3_13_1 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_12_4 y z w b u))+(((d2_8_1 y z w b u)*(d3_12_3 y z w b u))+((d2_8_2 y z w b u)*(d3_12_2 y z w b u))))+((((d2_9_0 y z w b u)*(d3_11_4 y z w b u))+((d2_9_1 y z w b u)*(d3_11_3 y z w b u)))+((d2_10_0 y z w b u)*(d3_10_4 y z w b u))))))))))))+((-1)*(d4_20_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_17_4,d0_18_4,d0_19_3,d0_19_4,d0_20_3,d0_20_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_1_4,d2_2_3,d2_2_4,d2_3_2,d2_3_3,d2_3_4,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_4,d3_11_3,d3_11_4,d3_12_2,d3_12_3,d3_12_4,d3_13_1,d3_13_2,d3_13_3,d3_13_4,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_20_4]
  ring
#print axioms coefficient_20_4
compact_certificate_declaration theorem coefficient_20_5 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[5]?=some 0 := by
  change some (((((((d0_17_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_18_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_19_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_19_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_20_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_20_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_1_5 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_2_4 y z w b u)*(d3_18_1 y z w b u))+(((d2_2_5 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_3_3 y z w b u)*(d3_17_2 y z w b u))+(((d2_3_4 y z w b u)*(d3_17_1 y z w b u))+(((d2_3_5 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_4_2 y z w b u)*(d3_16_3 y z w b u))+(((d2_4_3 y z w b u)*(d3_16_2 y z w b u))+(((d2_4_4 y z w b u)*(d3_16_1 y z w b u))+(((d2_4_5 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_5_1 y z w b u)*(d3_15_4 y z w b u))+(((d2_5_2 y z w b u)*(d3_15_3 y z w b u))+(((d2_5_3 y z w b u)*(d3_15_2 y z w b u))+(((d2_5_4 y z w b u)*(d3_15_1 y z w b u))+(((d2_5_5 y z w b u)*(d3_15_0 y z w b u))+0)))))+((((d2_6_1 y z w b u)*(d3_14_4 y z w b u))+(((d2_6_2 y z w b u)*(d3_14_3 y z w b u))+(((d2_6_3 y z w b u)*(d3_14_2 y z w b u))+((d2_6_4 y z w b u)*(d3_14_1 y z w b u)))))+((((d2_7_0 y z w b u)*(d3_13_5 y z w b u))+(((d2_7_1 y z w b u)*(d3_13_4 y z w b u))+(((d2_7_2 y z w b u)*(d3_13_3 y z w b u))+((d2_7_3 y z w b u)*(d3_13_2 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_12_5 y z w b u))+(((d2_8_1 y z w b u)*(d3_12_4 y z w b u))+((d2_8_2 y z w b u)*(d3_12_3 y z w b u))))+((((d2_9_0 y z w b u)*(d3_11_5 y z w b u))+((d2_9_1 y z w b u)*(d3_11_4 y z w b u)))+((d2_10_0 y z w b u)*(d3_10_5 y z w b u))))))))))))+((-1)*(d4_20_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_17_5,d0_18_5,d0_19_4,d0_19_5,d0_20_4,d0_20_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_1_5,d2_2_4,d2_2_5,d2_3_3,d2_3_4,d2_3_5,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_5,d3_11_4,d3_11_5,d3_12_3,d3_12_4,d3_12_5,d3_13_2,d3_13_3,d3_13_4,d3_13_5,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_20_5]
  ring
#print axioms coefficient_20_5

compact_certificate_declaration theorem coefficient_20_6 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[6]?=some 0 := by
  change some (((((((d0_17_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_18_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_19_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_19_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_20_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_20_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_2_5 y z w b u)*(d3_18_1 y z w b u))+((((d2_3_4 y z w b u)*(d3_17_2 y z w b u))+((d2_3_5 y z w b u)*(d3_17_1 y z w b u)))+((((d2_4_3 y z w b u)*(d3_16_3 y z w b u))+(((d2_4_4 y z w b u)*(d3_16_2 y z w b u))+((d2_4_5 y z w b u)*(d3_16_1 y z w b u))))+((((d2_5_2 y z w b u)*(d3_15_4 y z w b u))+(((d2_5_3 y z w b u)*(d3_15_3 y z w b u))+(((d2_5_4 y z w b u)*(d3_15_2 y z w b u))+((d2_5_5 y z w b u)*(d3_15_1 y z w b u)))))+((((d2_6_2 y z w b u)*(d3_14_4 y z w b u))+(((d2_6_3 y z w b u)*(d3_14_3 y z w b u))+((d2_6_4 y z w b u)*(d3_14_2 y z w b u))))+((((d2_7_1 y z w b u)*(d3_13_5 y z w b u))+(((d2_7_2 y z w b u)*(d3_13_4 y z w b u))+((d2_7_3 y z w b u)*(d3_13_3 y z w b u))))+((((d2_8_0 y z w b u)*(d3_12_6 y z w b u))+(((d2_8_1 y z w b u)*(d3_12_5 y z w b u))+((d2_8_2 y z w b u)*(d3_12_4 y z w b u))))+((((d2_9_0 y z w b u)*(d3_11_6 y z w b u))+((d2_9_1 y z w b u)*(d3_11_5 y z w b u)))+((d2_10_0 y z w b u)*(d3_10_6 y z w b u)))))))))))+((-1)*(d4_20_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_17_6,d0_18_6,d0_19_5,d0_19_6,d0_20_5,d0_20_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_2_5,d2_3_4,d2_3_5,d2_4_3,d2_4_4,d2_4_5,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_2,d2_6_3,d2_6_4,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_10_6,d3_11_5,d3_11_6,d3_12_4,d3_12_5,d3_12_6,d3_13_3,d3_13_4,d3_13_5,d3_14_2,d3_14_3,d3_14_4,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_1,d3_16_2,d3_16_3,d3_17_1,d3_17_2,d3_18_1,d4_20_6]
  ring
#print axioms coefficient_20_6
compact_certificate_declaration theorem coefficient_20_7 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[7]?=some 0 := by
  change some (((((((d0_17_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_18_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_19_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_19_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_20_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_20_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_3_5 y z w b u)*(d3_17_2 y z w b u))+((((d2_4_4 y z w b u)*(d3_16_3 y z w b u))+((d2_4_5 y z w b u)*(d3_16_2 y z w b u)))+((((d2_5_3 y z w b u)*(d3_15_4 y z w b u))+(((d2_5_4 y z w b u)*(d3_15_3 y z w b u))+((d2_5_5 y z w b u)*(d3_15_2 y z w b u))))+((((d2_6_3 y z w b u)*(d3_14_4 y z w b u))+((d2_6_4 y z w b u)*(d3_14_3 y z w b u)))+((((d2_7_2 y z w b u)*(d3_13_5 y z w b u))+((d2_7_3 y z w b u)*(d3_13_4 y z w b u)))+((((d2_8_1 y z w b u)*(d3_12_6 y z w b u))+((d2_8_2 y z w b u)*(d3_12_5 y z w b u)))+(((d2_9_1 y z w b u)*(d3_11_6 y z w b u))+((d2_10_0 y z w b u)*(d3_10_7 y z w b u))))))))))+((-1)*(d4_20_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_17_7,d0_18_7,d0_19_6,d0_19_7,d0_20_6,d0_20_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_3_5,d2_4_4,d2_4_5,d2_5_3,d2_5_4,d2_5_5,d2_6_3,d2_6_4,d2_7_2,d2_7_3,d2_8_1,d2_8_2,d2_9_1,d3_10_7,d3_11_6,d3_12_5,d3_12_6,d3_13_4,d3_13_5,d3_14_3,d3_14_4,d3_15_2,d3_15_3,d3_15_4,d3_16_2,d3_16_3,d3_17_2,d4_20_7]
  ring
#print axioms coefficient_20_7
compact_certificate_declaration theorem coefficient_20_8 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[8]?=some 0 := by
  change some (((((((d0_17_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_18_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_19_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_19_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_20_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_20_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_4_5 y z w b u)*(d3_16_3 y z w b u))+((((d2_5_4 y z w b u)*(d3_15_4 y z w b u))+((d2_5_5 y z w b u)*(d3_15_3 y z w b u)))+(((d2_6_4 y z w b u)*(d3_14_4 y z w b u))+(((d2_7_3 y z w b u)*(d3_13_5 y z w b u))+((d2_8_2 y z w b u)*(d3_12_6 y z w b u)))))))+((-1)*(d4_20_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_17_8,d0_18_8,d0_19_7,d0_19_8,d0_20_7,d0_20_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_4_5,d2_5_4,d2_5_5,d2_6_4,d2_7_3,d2_8_2,d3_12_6,d3_13_5,d3_14_4,d3_15_3,d3_15_4,d3_16_3,d4_20_8]
  ring
#print axioms coefficient_20_8

compact_certificate_declaration theorem coefficient_20_9 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[9]?=some 0 := by
  change some (((((((d0_17_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_18_9 y z w b u)*(d1_2_0 y z w b u))+0)+(((d0_19_8 y z w b u)*(d1_1_1 y z w b u))+((d0_20_8 y z w b u)*(d1_0_1 y z w b u)))))+((d2_5_5 y z w b u)*(d3_15_4 y z w b u)))+((-1)*(d4_20_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_17_9,d0_18_9,d0_19_8,d0_20_8,d1_0_1,d1_1_1,d1_2_0,d1_3_0,d2_5_5,d3_15_4,d4_20_9]
  ring
#print axioms coefficient_20_9

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
compact_certificate_declaration theorem inner_length_21 (y z w b u : ℂ) : (innerCertificate21 y z w b u).length=10 := by
  norm_num [innerCertificate21,add,multiply,scale,inner0_18,inner0_19,inner0_20,inner0_21,inner1_0,inner1_1,inner1_2,inner1_3,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner3_18,inner3_19,inner4_21]
compact_certificate_declaration theorem inner_eval_21 (y z w a b u : ℂ) :
    evaluate a (innerCertificate21 y z w b u)=(((((c0_18 y z w a b u)*(c1_3 y z w a b u))+(((c0_19 y z w a b u)*(c1_2 y z w a b u))+(((c0_20 y z w a b u)*(c1_1 y z w a b u))+(((c0_21 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_2 y z w a b u)*(c3_19 y z w a b u))+(((c2_3 y z w a b u)*(c3_18 y z w a b u))+(((c2_4 y z w a b u)*(c3_17 y z w a b u))+(((c2_5 y z w a b u)*(c3_16 y z w a b u))+(((c2_6 y z w a b u)*(c3_15 y z w a b u))+(((c2_7 y z w a b u)*(c3_14 y z w a b u))+(((c2_8 y z w a b u)*(c3_13 y z w a b u))+(((c2_9 y z w a b u)*(c3_12 y z w a b u))+((c2_10 y z w a b u)*(c3_11 y z w a b u)))))))))))+((-1)*(c4_21 y z w a b u))) := by
  simp only [innerCertificate21,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_18,c0_19,c0_20,c0_21,c1_0,c1_1,c1_2,c1_3,c2_10,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_18,c3_19,c4_21]
#print axioms inner_eval_21

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

compact_certificate_declaration theorem coefficient_21_0 (y z w b u : ℂ) :
    (innerCertificate21 y z w b u)[0]?=some 0 := by
  change some (((((((d0_18_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_19_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_20_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_21_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_18_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_17_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_16_0 y z w b u))+0)+((((d2_6_0 y z w b u)*(d3_15_0 y z w b u))+0)+((((d2_7_0 y z w b u)*(d3_14_0 y z w b u))+0)+((((d2_8_0 y z w b u)*(d3_13_0 y z w b u))+0)+((((d2_9_0 y z w b u)*(d3_12_0 y z w b u))+0)+(((d2_10_0 y z w b u)*(d3_11_0 y z w b u))+0))))))))))+(((-1)*(d4_21_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_18_0,d0_19_0,d0_20_0,d0_21_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_10_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d2_7_0,d2_8_0,d2_9_0,d3_11_0,d3_12_0,d3_13_0,d3_14_0,d3_15_0,d3_16_0,d3_17_0,d3_18_0,d3_19_0,d4_21_0]
  ring
#print axioms coefficient_21_0
compact_certificate_declaration theorem coefficient_21_1 (y z w b u : ℂ) :
    (innerCertificate21 y z w b u)[1]?=some 0 := by
  change some (((((((d0_18_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_19_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_20_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_20_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_21_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_21_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_2_1 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_18_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_17_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_16_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_16_0 y z w b u))+0))+((((d2_6_0 y z w b u)*(d3_15_1 y z w b u))+(((d2_6_1 y z w b u)*(d3_15_0 y z w b u))+0))+((((d2_7_0 y z w b u)*(d3_14_1 y z w b u))+(((d2_7_1 y z w b u)*(d3_14_0 y z w b u))+0))+((((d2_8_0 y z w b u)*(d3_13_1 y z w b u))+(((d2_8_1 y z w b u)*(d3_13_0 y z w b u))+0))+((((d2_9_0 y z w b u)*(d3_12_1 y z w b u))+(((d2_9_1 y z w b u)*(d3_12_0 y z w b u))+0))+((d2_10_0 y z w b u)*(d3_11_1 y z w b u)))))))))))+((-1)*(d4_21_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_18_1,d0_19_1,d0_20_0,d0_20_1,d0_21_0,d0_21_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d2_6_1,d2_7_0,d2_7_1,d2_8_0,d2_8_1,d2_9_0,d2_9_1,d3_11_1,d3_12_0,d3_12_1,d3_13_0,d3_13_1,d3_14_0,d3_14_1,d3_15_0,d3_15_1,d3_16_0,d3_16_1,d3_17_0,d3_17_1,d3_18_0,d3_18_1,d3_19_0,d4_21_1]
  ring
#print axioms coefficient_21_1
compact_certificate_declaration theorem coefficient_21_2 (y z w b u : ℂ) :
    (innerCertificate21 y z w b u)[2]?=some 0 := by
  change some (((((((d0_18_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_19_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_20_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_20_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_21_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_21_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_2_2 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_3_1 y z w b u)*(d3_18_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_17_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_17_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_16_2 y z w b u))+(((d2_5_1 y z w b u)*(d3_16_1 y z w b u))+(((d2_5_2 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_6_0 y z w b u)*(d3_15_2 y z w b u))+(((d2_6_1 y z w b u)*(d3_15_1 y z w b u))+(((d2_6_2 y z w b u)*(d3_15_0 y z w b u))+0)))+((((d2_7_0 y z w b u)*(d3_14_2 y z w b u))+(((d2_7_1 y z w b u)*(d3_14_1 y z w b u))+(((d2_7_2 y z w b u)*(d3_14_0 y z w b u))+0)))+((((d2_8_0 y z w b u)*(d3_13_2 y z w b u))+(((d2_8_1 y z w b u)*(d3_13_1 y z w b u))+(((d2_8_2 y z w b u)*(d3_13_0 y z w b u))+0)))+((((d2_9_0 y z w b u)*(d3_12_2 y z w b u))+((d2_9_1 y z w b u)*(d3_12_1 y z w b u)))+((d2_10_0 y z w b u)*(d3_11_2 y z w b u)))))))))))+((-1)*(d4_21_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_18_2,d0_19_2,d0_20_1,d0_20_2,d0_21_1,d0_21_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_2_2,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_5_2,d2_6_0,d2_6_1,d2_6_2,d2_7_0,d2_7_1,d2_7_2,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_11_2,d3_12_1,d3_12_2,d3_13_0,d3_13_1,d3_13_2,d3_14_0,d3_14_1,d3_14_2,d3_15_0,d3_15_1,d3_15_2,d3_16_0,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_21_2]
  ring
#print axioms coefficient_21_2

compact_certificate_declaration theorem coefficient_21_3 (y z w b u : ℂ) :
    (innerCertificate21 y z w b u)[3]?=some 0 := by
  change some (((((((d0_18_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_19_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_20_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_20_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_21_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_21_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_2_3 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_3_2 y z w b u)*(d3_18_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_4_1 y z w b u)*(d3_17_2 y z w b u))+(((d2_4_2 y z w b u)*(d3_17_1 y z w b u))+(((d2_4_3 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_16_3 y z w b u))+(((d2_5_1 y z w b u)*(d3_16_2 y z w b u))+(((d2_5_2 y z w b u)*(d3_16_1 y z w b u))+(((d2_5_3 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_6_0 y z w b u)*(d3_15_3 y z w b u))+(((d2_6_1 y z w b u)*(d3_15_2 y z w b u))+(((d2_6_2 y z w b u)*(d3_15_1 y z w b u))+(((d2_6_3 y z w b u)*(d3_15_0 y z w b u))+0))))+((((d2_7_0 y z w b u)*(d3_14_3 y z w b u))+(((d2_7_1 y z w b u)*(d3_14_2 y z w b u))+(((d2_7_2 y z w b u)*(d3_14_1 y z w b u))+(((d2_7_3 y z w b u)*(d3_14_0 y z w b u))+0))))+((((d2_8_0 y z w b u)*(d3_13_3 y z w b u))+(((d2_8_1 y z w b u)*(d3_13_2 y z w b u))+((d2_8_2 y z w b u)*(d3_13_1 y z w b u))))+((((d2_9_0 y z w b u)*(d3_12_3 y z w b u))+((d2_9_1 y z w b u)*(d3_12_2 y z w b u)))+((d2_10_0 y z w b u)*(d3_11_3 y z w b u)))))))))))+((-1)*(d4_21_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_18_3,d0_19_3,d0_20_2,d0_20_3,d0_21_2,d0_21_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_2_3,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d2_4_3,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_11_3,d3_12_2,d3_12_3,d3_13_1,d3_13_2,d3_13_3,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_21_3]
  ring
#print axioms coefficient_21_3
compact_certificate_declaration theorem coefficient_21_4 (y z w b u : ℂ) :
    (innerCertificate21 y z w b u)[4]?=some 0 := by
  change some (((((((d0_18_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_19_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_20_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_20_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_21_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_21_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_2_4 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_3_3 y z w b u)*(d3_18_1 y z w b u))+(((d2_3_4 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_4_2 y z w b u)*(d3_17_2 y z w b u))+(((d2_4_3 y z w b u)*(d3_17_1 y z w b u))+(((d2_4_4 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_5_1 y z w b u)*(d3_16_3 y z w b u))+(((d2_5_2 y z w b u)*(d3_16_2 y z w b u))+(((d2_5_3 y z w b u)*(d3_16_1 y z w b u))+(((d2_5_4 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_6_0 y z w b u)*(d3_15_4 y z w b u))+(((d2_6_1 y z w b u)*(d3_15_3 y z w b u))+(((d2_6_2 y z w b u)*(d3_15_2 y z w b u))+(((d2_6_3 y z w b u)*(d3_15_1 y z w b u))+(((d2_6_4 y z w b u)*(d3_15_0 y z w b u))+0)))))+((((d2_7_0 y z w b u)*(d3_14_4 y z w b u))+(((d2_7_1 y z w b u)*(d3_14_3 y z w b u))+(((d2_7_2 y z w b u)*(d3_14_2 y z w b u))+((d2_7_3 y z w b u)*(d3_14_1 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_13_4 y z w b u))+(((d2_8_1 y z w b u)*(d3_13_3 y z w b u))+((d2_8_2 y z w b u)*(d3_13_2 y z w b u))))+((((d2_9_0 y z w b u)*(d3_12_4 y z w b u))+((d2_9_1 y z w b u)*(d3_12_3 y z w b u)))+((d2_10_0 y z w b u)*(d3_11_4 y z w b u)))))))))))+((-1)*(d4_21_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_18_4,d0_19_4,d0_20_3,d0_20_4,d0_21_3,d0_21_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_2_4,d2_3_3,d2_3_4,d2_4_2,d2_4_3,d2_4_4,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_11_4,d3_12_3,d3_12_4,d3_13_2,d3_13_3,d3_13_4,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_21_4]
  ring
#print axioms coefficient_21_4
compact_certificate_declaration theorem coefficient_21_5 (y z w b u : ℂ) :
    (innerCertificate21 y z w b u)[5]?=some 0 := by
  change some (((((((d0_18_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_19_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_20_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_20_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_21_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_21_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_2_5 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_3_4 y z w b u)*(d3_18_1 y z w b u))+(((d2_3_5 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_4_3 y z w b u)*(d3_17_2 y z w b u))+(((d2_4_4 y z w b u)*(d3_17_1 y z w b u))+(((d2_4_5 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_5_2 y z w b u)*(d3_16_3 y z w b u))+(((d2_5_3 y z w b u)*(d3_16_2 y z w b u))+(((d2_5_4 y z w b u)*(d3_16_1 y z w b u))+(((d2_5_5 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_6_1 y z w b u)*(d3_15_4 y z w b u))+(((d2_6_2 y z w b u)*(d3_15_3 y z w b u))+(((d2_6_3 y z w b u)*(d3_15_2 y z w b u))+((d2_6_4 y z w b u)*(d3_15_1 y z w b u)))))+((((d2_7_1 y z w b u)*(d3_14_4 y z w b u))+(((d2_7_2 y z w b u)*(d3_14_3 y z w b u))+((d2_7_3 y z w b u)*(d3_14_2 y z w b u))))+((((d2_8_0 y z w b u)*(d3_13_5 y z w b u))+(((d2_8_1 y z w b u)*(d3_13_4 y z w b u))+((d2_8_2 y z w b u)*(d3_13_3 y z w b u))))+((((d2_9_0 y z w b u)*(d3_12_5 y z w b u))+((d2_9_1 y z w b u)*(d3_12_4 y z w b u)))+((d2_10_0 y z w b u)*(d3_11_5 y z w b u)))))))))))+((-1)*(d4_21_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_18_5,d0_19_5,d0_20_4,d0_20_5,d0_21_4,d0_21_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_2_5,d2_3_4,d2_3_5,d2_4_3,d2_4_4,d2_4_5,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_11_5,d3_12_4,d3_12_5,d3_13_3,d3_13_4,d3_13_5,d3_14_2,d3_14_3,d3_14_4,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_21_5]
  ring
#print axioms coefficient_21_5

compact_certificate_declaration theorem coefficient_21_6 (y z w b u : ℂ) :
    (innerCertificate21 y z w b u)[6]?=some 0 := by
  change some (((((((d0_18_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_19_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_20_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_20_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_21_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_21_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_3_5 y z w b u)*(d3_18_1 y z w b u))+((((d2_4_4 y z w b u)*(d3_17_2 y z w b u))+((d2_4_5 y z w b u)*(d3_17_1 y z w b u)))+((((d2_5_3 y z w b u)*(d3_16_3 y z w b u))+(((d2_5_4 y z w b u)*(d3_16_2 y z w b u))+((d2_5_5 y z w b u)*(d3_16_1 y z w b u))))+((((d2_6_2 y z w b u)*(d3_15_4 y z w b u))+(((d2_6_3 y z w b u)*(d3_15_3 y z w b u))+((d2_6_4 y z w b u)*(d3_15_2 y z w b u))))+((((d2_7_2 y z w b u)*(d3_14_4 y z w b u))+((d2_7_3 y z w b u)*(d3_14_3 y z w b u)))+((((d2_8_1 y z w b u)*(d3_13_5 y z w b u))+((d2_8_2 y z w b u)*(d3_13_4 y z w b u)))+((((d2_9_0 y z w b u)*(d3_12_6 y z w b u))+((d2_9_1 y z w b u)*(d3_12_5 y z w b u)))+((d2_10_0 y z w b u)*(d3_11_6 y z w b u))))))))))+((-1)*(d4_21_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_18_6,d0_19_6,d0_20_5,d0_20_6,d0_21_5,d0_21_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_3_5,d2_4_4,d2_4_5,d2_5_3,d2_5_4,d2_5_5,d2_6_2,d2_6_3,d2_6_4,d2_7_2,d2_7_3,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_11_6,d3_12_5,d3_12_6,d3_13_4,d3_13_5,d3_14_3,d3_14_4,d3_15_2,d3_15_3,d3_15_4,d3_16_1,d3_16_2,d3_16_3,d3_17_1,d3_17_2,d3_18_1,d4_21_6]
  ring
#print axioms coefficient_21_6
compact_certificate_declaration theorem coefficient_21_7 (y z w b u : ℂ) :
    (innerCertificate21 y z w b u)[7]?=some 0 := by
  change some (((((((d0_18_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_19_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_20_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_20_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_21_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_21_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_4_5 y z w b u)*(d3_17_2 y z w b u))+((((d2_5_4 y z w b u)*(d3_16_3 y z w b u))+((d2_5_5 y z w b u)*(d3_16_2 y z w b u)))+((((d2_6_3 y z w b u)*(d3_15_4 y z w b u))+((d2_6_4 y z w b u)*(d3_15_3 y z w b u)))+(((d2_7_3 y z w b u)*(d3_14_4 y z w b u))+(((d2_8_2 y z w b u)*(d3_13_5 y z w b u))+((d2_9_1 y z w b u)*(d3_12_6 y z w b u))))))))+((-1)*(d4_21_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_18_7,d0_19_7,d0_20_6,d0_20_7,d0_21_6,d0_21_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_4_5,d2_5_4,d2_5_5,d2_6_3,d2_6_4,d2_7_3,d2_8_2,d2_9_1,d3_12_6,d3_13_5,d3_14_4,d3_15_3,d3_15_4,d3_16_2,d3_16_3,d3_17_2,d4_21_7]
  ring
#print axioms coefficient_21_7
compact_certificate_declaration theorem coefficient_21_8 (y z w b u : ℂ) :
    (innerCertificate21 y z w b u)[8]?=some 0 := by
  change some (((((((d0_18_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_19_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_20_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_20_8 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_21_7 y z w b u)*(d1_0_1 y z w b u)))))+(((d2_5_5 y z w b u)*(d3_16_3 y z w b u))+((d2_6_4 y z w b u)*(d3_15_4 y z w b u))))+((-1)*(d4_21_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_18_8,d0_19_8,d0_20_7,d0_20_8,d0_21_7,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_5_5,d2_6_4,d3_15_4,d3_16_3,d4_21_8]
  ring
#print axioms coefficient_21_8

compact_certificate_declaration theorem coefficient_21_9 (y z w b u : ℂ) :
    (innerCertificate21 y z w b u)[9]?=some 0 := by
  change some (((((d0_18_9 y z w b u)*(d1_3_0 y z w b u))+0)+((d0_20_8 y z w b u)*(d1_1_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_18_9,d0_20_8,d1_1_1,d1_3_0]
  ring
#print axioms coefficient_21_9

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
compact_certificate_declaration theorem inner_length_22 (y z w b u : ℂ) : (innerCertificate22 y z w b u).length=9 := by
  norm_num [innerCertificate22,add,multiply,scale,inner0_19,inner0_20,inner0_21,inner0_22,inner1_0,inner1_1,inner1_2,inner1_3,inner2_10,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner3_18,inner3_19,inner4_22]
compact_certificate_declaration theorem inner_eval_22 (y z w a b u : ℂ) :
    evaluate a (innerCertificate22 y z w b u)=(((((c0_19 y z w a b u)*(c1_3 y z w a b u))+(((c0_20 y z w a b u)*(c1_2 y z w a b u))+(((c0_21 y z w a b u)*(c1_1 y z w a b u))+(((c0_22 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_3 y z w a b u)*(c3_19 y z w a b u))+(((c2_4 y z w a b u)*(c3_18 y z w a b u))+(((c2_5 y z w a b u)*(c3_17 y z w a b u))+(((c2_6 y z w a b u)*(c3_16 y z w a b u))+(((c2_7 y z w a b u)*(c3_15 y z w a b u))+(((c2_8 y z w a b u)*(c3_14 y z w a b u))+(((c2_9 y z w a b u)*(c3_13 y z w a b u))+((c2_10 y z w a b u)*(c3_12 y z w a b u))))))))))+((-1)*(c4_22 y z w a b u))) := by
  simp only [innerCertificate22,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_19,c0_20,c0_21,c0_22,c1_0,c1_1,c1_2,c1_3,c2_10,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_18,c3_19,c4_22]
#print axioms inner_eval_22

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

compact_certificate_declaration theorem coefficient_22_0 (y z w b u : ℂ) :
    (innerCertificate22 y z w b u)[0]?=some 0 := by
  change some (((((((d0_19_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_20_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_21_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_22_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_18_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_17_0 y z w b u))+0)+((((d2_6_0 y z w b u)*(d3_16_0 y z w b u))+0)+((((d2_7_0 y z w b u)*(d3_15_0 y z w b u))+0)+((((d2_8_0 y z w b u)*(d3_14_0 y z w b u))+0)+((((d2_9_0 y z w b u)*(d3_13_0 y z w b u))+0)+(((d2_10_0 y z w b u)*(d3_12_0 y z w b u))+0)))))))))+(((-1)*(d4_22_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_19_0,d0_20_0,d0_21_0,d0_22_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_10_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d2_7_0,d2_8_0,d2_9_0,d3_12_0,d3_13_0,d3_14_0,d3_15_0,d3_16_0,d3_17_0,d3_18_0,d3_19_0,d4_22_0]
  ring
#print axioms coefficient_22_0
compact_certificate_declaration theorem coefficient_22_1 (y z w b u : ℂ) :
    (innerCertificate22 y z w b u)[1]?=some 0 := by
  change some (((((((d0_19_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_20_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_21_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_21_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_22_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_22_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_3_1 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_18_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_17_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_6_0 y z w b u)*(d3_16_1 y z w b u))+(((d2_6_1 y z w b u)*(d3_16_0 y z w b u))+0))+((((d2_7_0 y z w b u)*(d3_15_1 y z w b u))+(((d2_7_1 y z w b u)*(d3_15_0 y z w b u))+0))+((((d2_8_0 y z w b u)*(d3_14_1 y z w b u))+(((d2_8_1 y z w b u)*(d3_14_0 y z w b u))+0))+((((d2_9_0 y z w b u)*(d3_13_1 y z w b u))+(((d2_9_1 y z w b u)*(d3_13_0 y z w b u))+0))+((d2_10_0 y z w b u)*(d3_12_1 y z w b u))))))))))+((-1)*(d4_22_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_19_1,d0_20_1,d0_21_0,d0_21_1,d0_22_0,d0_22_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d2_6_1,d2_7_0,d2_7_1,d2_8_0,d2_8_1,d2_9_0,d2_9_1,d3_12_1,d3_13_0,d3_13_1,d3_14_0,d3_14_1,d3_15_0,d3_15_1,d3_16_0,d3_16_1,d3_17_0,d3_17_1,d3_18_0,d3_18_1,d3_19_0,d4_22_1]
  ring
#print axioms coefficient_22_1
compact_certificate_declaration theorem coefficient_22_2 (y z w b u : ℂ) :
    (innerCertificate22 y z w b u)[2]?=some 0 := by
  change some (((((((d0_19_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_20_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_21_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_21_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_22_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_22_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_3_2 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_4_1 y z w b u)*(d3_18_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_17_2 y z w b u))+(((d2_5_1 y z w b u)*(d3_17_1 y z w b u))+(((d2_5_2 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_6_0 y z w b u)*(d3_16_2 y z w b u))+(((d2_6_1 y z w b u)*(d3_16_1 y z w b u))+(((d2_6_2 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_7_0 y z w b u)*(d3_15_2 y z w b u))+(((d2_7_1 y z w b u)*(d3_15_1 y z w b u))+(((d2_7_2 y z w b u)*(d3_15_0 y z w b u))+0)))+((((d2_8_0 y z w b u)*(d3_14_2 y z w b u))+(((d2_8_1 y z w b u)*(d3_14_1 y z w b u))+(((d2_8_2 y z w b u)*(d3_14_0 y z w b u))+0)))+((((d2_9_0 y z w b u)*(d3_13_2 y z w b u))+((d2_9_1 y z w b u)*(d3_13_1 y z w b u)))+((d2_10_0 y z w b u)*(d3_12_2 y z w b u))))))))))+((-1)*(d4_22_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_19_2,d0_20_2,d0_21_1,d0_21_2,d0_22_1,d0_22_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_3_2,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_5_2,d2_6_0,d2_6_1,d2_6_2,d2_7_0,d2_7_1,d2_7_2,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_12_2,d3_13_1,d3_13_2,d3_14_0,d3_14_1,d3_14_2,d3_15_0,d3_15_1,d3_15_2,d3_16_0,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_22_2]
  ring
#print axioms coefficient_22_2

compact_certificate_declaration theorem coefficient_22_3 (y z w b u : ℂ) :
    (innerCertificate22 y z w b u)[3]?=some 0 := by
  change some (((((((d0_19_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_20_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_21_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_21_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_22_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_22_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_3_3 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_4_2 y z w b u)*(d3_18_1 y z w b u))+(((d2_4_3 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_5_1 y z w b u)*(d3_17_2 y z w b u))+(((d2_5_2 y z w b u)*(d3_17_1 y z w b u))+(((d2_5_3 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_6_0 y z w b u)*(d3_16_3 y z w b u))+(((d2_6_1 y z w b u)*(d3_16_2 y z w b u))+(((d2_6_2 y z w b u)*(d3_16_1 y z w b u))+(((d2_6_3 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_7_0 y z w b u)*(d3_15_3 y z w b u))+(((d2_7_1 y z w b u)*(d3_15_2 y z w b u))+(((d2_7_2 y z w b u)*(d3_15_1 y z w b u))+(((d2_7_3 y z w b u)*(d3_15_0 y z w b u))+0))))+((((d2_8_0 y z w b u)*(d3_14_3 y z w b u))+(((d2_8_1 y z w b u)*(d3_14_2 y z w b u))+((d2_8_2 y z w b u)*(d3_14_1 y z w b u))))+((((d2_9_0 y z w b u)*(d3_13_3 y z w b u))+((d2_9_1 y z w b u)*(d3_13_2 y z w b u)))+((d2_10_0 y z w b u)*(d3_12_3 y z w b u))))))))))+((-1)*(d4_22_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_19_3,d0_20_3,d0_21_2,d0_21_3,d0_22_2,d0_22_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_3_3,d2_4_2,d2_4_3,d2_5_1,d2_5_2,d2_5_3,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_12_3,d3_13_2,d3_13_3,d3_14_1,d3_14_2,d3_14_3,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_22_3]
  ring
#print axioms coefficient_22_3
compact_certificate_declaration theorem coefficient_22_4 (y z w b u : ℂ) :
    (innerCertificate22 y z w b u)[4]?=some 0 := by
  change some (((((((d0_19_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_20_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_21_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_21_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_22_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_22_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_3_4 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_4_3 y z w b u)*(d3_18_1 y z w b u))+(((d2_4_4 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_5_2 y z w b u)*(d3_17_2 y z w b u))+(((d2_5_3 y z w b u)*(d3_17_1 y z w b u))+(((d2_5_4 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_6_1 y z w b u)*(d3_16_3 y z w b u))+(((d2_6_2 y z w b u)*(d3_16_2 y z w b u))+(((d2_6_3 y z w b u)*(d3_16_1 y z w b u))+(((d2_6_4 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_7_0 y z w b u)*(d3_15_4 y z w b u))+(((d2_7_1 y z w b u)*(d3_15_3 y z w b u))+(((d2_7_2 y z w b u)*(d3_15_2 y z w b u))+((d2_7_3 y z w b u)*(d3_15_1 y z w b u)))))+((((d2_8_0 y z w b u)*(d3_14_4 y z w b u))+(((d2_8_1 y z w b u)*(d3_14_3 y z w b u))+((d2_8_2 y z w b u)*(d3_14_2 y z w b u))))+((((d2_9_0 y z w b u)*(d3_13_4 y z w b u))+((d2_9_1 y z w b u)*(d3_13_3 y z w b u)))+((d2_10_0 y z w b u)*(d3_12_4 y z w b u))))))))))+((-1)*(d4_22_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_19_4,d0_20_4,d0_21_3,d0_21_4,d0_22_3,d0_22_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_3_4,d2_4_3,d2_4_4,d2_5_2,d2_5_3,d2_5_4,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_12_4,d3_13_3,d3_13_4,d3_14_2,d3_14_3,d3_14_4,d3_15_1,d3_15_2,d3_15_3,d3_15_4,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_22_4]
  ring
#print axioms coefficient_22_4
compact_certificate_declaration theorem coefficient_22_5 (y z w b u : ℂ) :
    (innerCertificate22 y z w b u)[5]?=some 0 := by
  change some (((((((d0_19_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_20_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_21_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_21_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_22_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_22_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_3_5 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_4_4 y z w b u)*(d3_18_1 y z w b u))+(((d2_4_5 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_5_3 y z w b u)*(d3_17_2 y z w b u))+(((d2_5_4 y z w b u)*(d3_17_1 y z w b u))+(((d2_5_5 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_6_2 y z w b u)*(d3_16_3 y z w b u))+(((d2_6_3 y z w b u)*(d3_16_2 y z w b u))+((d2_6_4 y z w b u)*(d3_16_1 y z w b u))))+((((d2_7_1 y z w b u)*(d3_15_4 y z w b u))+(((d2_7_2 y z w b u)*(d3_15_3 y z w b u))+((d2_7_3 y z w b u)*(d3_15_2 y z w b u))))+((((d2_8_1 y z w b u)*(d3_14_4 y z w b u))+((d2_8_2 y z w b u)*(d3_14_3 y z w b u)))+((((d2_9_0 y z w b u)*(d3_13_5 y z w b u))+((d2_9_1 y z w b u)*(d3_13_4 y z w b u)))+((d2_10_0 y z w b u)*(d3_12_5 y z w b u))))))))))+((-1)*(d4_22_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_19_5,d0_20_5,d0_21_4,d0_21_5,d0_22_4,d0_22_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_3_5,d2_4_4,d2_4_5,d2_5_3,d2_5_4,d2_5_5,d2_6_2,d2_6_3,d2_6_4,d2_7_1,d2_7_2,d2_7_3,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_12_5,d3_13_4,d3_13_5,d3_14_3,d3_14_4,d3_15_2,d3_15_3,d3_15_4,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_22_5]
  ring
#print axioms coefficient_22_5

compact_certificate_declaration theorem coefficient_22_6 (y z w b u : ℂ) :
    (innerCertificate22 y z w b u)[6]?=some 0 := by
  change some (((((((d0_19_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_20_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_21_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_21_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_22_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_22_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_4_5 y z w b u)*(d3_18_1 y z w b u))+((((d2_5_4 y z w b u)*(d3_17_2 y z w b u))+((d2_5_5 y z w b u)*(d3_17_1 y z w b u)))+((((d2_6_3 y z w b u)*(d3_16_3 y z w b u))+((d2_6_4 y z w b u)*(d3_16_2 y z w b u)))+((((d2_7_2 y z w b u)*(d3_15_4 y z w b u))+((d2_7_3 y z w b u)*(d3_15_3 y z w b u)))+(((d2_8_2 y z w b u)*(d3_14_4 y z w b u))+(((d2_9_1 y z w b u)*(d3_13_5 y z w b u))+((d2_10_0 y z w b u)*(d3_12_6 y z w b u)))))))))+((-1)*(d4_22_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_19_6,d0_20_6,d0_21_5,d0_21_6,d0_22_5,d0_22_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_4_5,d2_5_4,d2_5_5,d2_6_3,d2_6_4,d2_7_2,d2_7_3,d2_8_2,d2_9_1,d3_12_6,d3_13_5,d3_14_4,d3_15_3,d3_15_4,d3_16_2,d3_16_3,d3_17_1,d3_17_2,d3_18_1,d4_22_6]
  ring
#print axioms coefficient_22_6
compact_certificate_declaration theorem coefficient_22_7 (y z w b u : ℂ) :
    (innerCertificate22 y z w b u)[7]?=some 0 := by
  change some (((((((d0_19_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_20_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_21_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_21_7 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_22_6 y z w b u)*(d1_0_1 y z w b u)))))+(((d2_5_5 y z w b u)*(d3_17_2 y z w b u))+(((d2_6_4 y z w b u)*(d3_16_3 y z w b u))+((d2_7_3 y z w b u)*(d3_15_4 y z w b u)))))+((-1)*(d4_22_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_19_7,d0_20_7,d0_21_6,d0_21_7,d0_22_6,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_5_5,d2_6_4,d2_7_3,d3_15_4,d3_16_3,d3_17_2,d4_22_7]
  ring
#print axioms coefficient_22_7
compact_certificate_declaration theorem coefficient_22_8 (y z w b u : ℂ) :
    (innerCertificate22 y z w b u)[8]?=some 0 := by
  change some ((((((d0_19_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_20_8 y z w b u)*(d1_2_0 y z w b u))+0)+((d0_21_7 y z w b u)*(d1_1_1 y z w b u))))+((-1)*(d4_22_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_19_8,d0_20_8,d0_21_7,d1_1_1,d1_2_0,d1_3_0,d4_22_8]
  ring
#print axioms coefficient_22_8

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
compact_certificate_declaration theorem inner_length_23 (y z w b u : ℂ) : (innerCertificate23 y z w b u).length=9 := by
  norm_num [innerCertificate23,add,multiply,scale,inner0_20,inner0_21,inner0_22,inner0_23,inner1_0,inner1_1,inner1_2,inner1_3,inner2_10,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner3_18,inner3_19,inner4_23]
compact_certificate_declaration theorem inner_eval_23 (y z w a b u : ℂ) :
    evaluate a (innerCertificate23 y z w b u)=(((((c0_20 y z w a b u)*(c1_3 y z w a b u))+(((c0_21 y z w a b u)*(c1_2 y z w a b u))+(((c0_22 y z w a b u)*(c1_1 y z w a b u))+(((c0_23 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_4 y z w a b u)*(c3_19 y z w a b u))+(((c2_5 y z w a b u)*(c3_18 y z w a b u))+(((c2_6 y z w a b u)*(c3_17 y z w a b u))+(((c2_7 y z w a b u)*(c3_16 y z w a b u))+(((c2_8 y z w a b u)*(c3_15 y z w a b u))+(((c2_9 y z w a b u)*(c3_14 y z w a b u))+((c2_10 y z w a b u)*(c3_13 y z w a b u)))))))))+((-1)*(c4_23 y z w a b u))) := by
  simp only [innerCertificate23,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_20,c0_21,c0_22,c0_23,c1_0,c1_1,c1_2,c1_3,c2_10,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_13,c3_14,c3_15,c3_16,c3_17,c3_18,c3_19,c4_23]
#print axioms inner_eval_23

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

compact_certificate_declaration theorem coefficient_23_0 (y z w b u : ℂ) :
    (innerCertificate23 y z w b u)[0]?=some 0 := by
  change some (((((((d0_20_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_21_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_22_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_23_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_18_0 y z w b u))+0)+((((d2_6_0 y z w b u)*(d3_17_0 y z w b u))+0)+((((d2_7_0 y z w b u)*(d3_16_0 y z w b u))+0)+((((d2_8_0 y z w b u)*(d3_15_0 y z w b u))+0)+((((d2_9_0 y z w b u)*(d3_14_0 y z w b u))+0)+(((d2_10_0 y z w b u)*(d3_13_0 y z w b u))+0))))))))+(((-1)*(d4_23_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_20_0,d0_21_0,d0_22_0,d0_23_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_10_0,d2_4_0,d2_5_0,d2_6_0,d2_7_0,d2_8_0,d2_9_0,d3_13_0,d3_14_0,d3_15_0,d3_16_0,d3_17_0,d3_18_0,d3_19_0,d4_23_0]
  ring
#print axioms coefficient_23_0
compact_certificate_declaration theorem coefficient_23_1 (y z w b u : ℂ) :
    (innerCertificate23 y z w b u)[1]?=some 0 := by
  change some (((((((d0_20_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_21_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_22_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_22_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_23_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_23_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_4_1 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_18_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_6_0 y z w b u)*(d3_17_1 y z w b u))+(((d2_6_1 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_7_0 y z w b u)*(d3_16_1 y z w b u))+(((d2_7_1 y z w b u)*(d3_16_0 y z w b u))+0))+((((d2_8_0 y z w b u)*(d3_15_1 y z w b u))+(((d2_8_1 y z w b u)*(d3_15_0 y z w b u))+0))+((((d2_9_0 y z w b u)*(d3_14_1 y z w b u))+(((d2_9_1 y z w b u)*(d3_14_0 y z w b u))+0))+((d2_10_0 y z w b u)*(d3_13_1 y z w b u)))))))))+((-1)*(d4_23_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_20_1,d0_21_1,d0_22_0,d0_22_1,d0_23_0,d0_23_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d2_6_1,d2_7_0,d2_7_1,d2_8_0,d2_8_1,d2_9_0,d2_9_1,d3_13_1,d3_14_0,d3_14_1,d3_15_0,d3_15_1,d3_16_0,d3_16_1,d3_17_0,d3_17_1,d3_18_0,d3_18_1,d3_19_0,d4_23_1]
  ring
#print axioms coefficient_23_1
compact_certificate_declaration theorem coefficient_23_2 (y z w b u : ℂ) :
    (innerCertificate23 y z w b u)[2]?=some 0 := by
  change some (((((((d0_20_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_21_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_22_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_22_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_23_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_23_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_4_2 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_5_1 y z w b u)*(d3_18_1 y z w b u))+(((d2_5_2 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_6_0 y z w b u)*(d3_17_2 y z w b u))+(((d2_6_1 y z w b u)*(d3_17_1 y z w b u))+(((d2_6_2 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_7_0 y z w b u)*(d3_16_2 y z w b u))+(((d2_7_1 y z w b u)*(d3_16_1 y z w b u))+(((d2_7_2 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_8_0 y z w b u)*(d3_15_2 y z w b u))+(((d2_8_1 y z w b u)*(d3_15_1 y z w b u))+(((d2_8_2 y z w b u)*(d3_15_0 y z w b u))+0)))+((((d2_9_0 y z w b u)*(d3_14_2 y z w b u))+((d2_9_1 y z w b u)*(d3_14_1 y z w b u)))+((d2_10_0 y z w b u)*(d3_13_2 y z w b u)))))))))+((-1)*(d4_23_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_20_2,d0_21_2,d0_22_1,d0_22_2,d0_23_1,d0_23_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_4_2,d2_5_1,d2_5_2,d2_6_0,d2_6_1,d2_6_2,d2_7_0,d2_7_1,d2_7_2,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_13_2,d3_14_1,d3_14_2,d3_15_0,d3_15_1,d3_15_2,d3_16_0,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_23_2]
  ring
#print axioms coefficient_23_2

compact_certificate_declaration theorem coefficient_23_3 (y z w b u : ℂ) :
    (innerCertificate23 y z w b u)[3]?=some 0 := by
  change some (((((((d0_20_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_21_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_22_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_22_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_23_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_23_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_4_3 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_5_2 y z w b u)*(d3_18_1 y z w b u))+(((d2_5_3 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_6_1 y z w b u)*(d3_17_2 y z w b u))+(((d2_6_2 y z w b u)*(d3_17_1 y z w b u))+(((d2_6_3 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_7_0 y z w b u)*(d3_16_3 y z w b u))+(((d2_7_1 y z w b u)*(d3_16_2 y z w b u))+(((d2_7_2 y z w b u)*(d3_16_1 y z w b u))+(((d2_7_3 y z w b u)*(d3_16_0 y z w b u))+0))))+((((d2_8_0 y z w b u)*(d3_15_3 y z w b u))+(((d2_8_1 y z w b u)*(d3_15_2 y z w b u))+((d2_8_2 y z w b u)*(d3_15_1 y z w b u))))+((((d2_9_0 y z w b u)*(d3_14_3 y z w b u))+((d2_9_1 y z w b u)*(d3_14_2 y z w b u)))+((d2_10_0 y z w b u)*(d3_13_3 y z w b u)))))))))+((-1)*(d4_23_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_20_3,d0_21_3,d0_22_2,d0_22_3,d0_23_2,d0_23_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_4_3,d2_5_2,d2_5_3,d2_6_1,d2_6_2,d2_6_3,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_13_3,d3_14_2,d3_14_3,d3_15_1,d3_15_2,d3_15_3,d3_16_0,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_23_3]
  ring
#print axioms coefficient_23_3
compact_certificate_declaration theorem coefficient_23_4 (y z w b u : ℂ) :
    (innerCertificate23 y z w b u)[4]?=some 0 := by
  change some (((((((d0_20_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_21_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_22_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_22_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_23_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_23_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_4_4 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_5_3 y z w b u)*(d3_18_1 y z w b u))+(((d2_5_4 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_6_2 y z w b u)*(d3_17_2 y z w b u))+(((d2_6_3 y z w b u)*(d3_17_1 y z w b u))+(((d2_6_4 y z w b u)*(d3_17_0 y z w b u))+0)))+((((d2_7_1 y z w b u)*(d3_16_3 y z w b u))+(((d2_7_2 y z w b u)*(d3_16_2 y z w b u))+((d2_7_3 y z w b u)*(d3_16_1 y z w b u))))+((((d2_8_0 y z w b u)*(d3_15_4 y z w b u))+(((d2_8_1 y z w b u)*(d3_15_3 y z w b u))+((d2_8_2 y z w b u)*(d3_15_2 y z w b u))))+((((d2_9_0 y z w b u)*(d3_14_4 y z w b u))+((d2_9_1 y z w b u)*(d3_14_3 y z w b u)))+((d2_10_0 y z w b u)*(d3_13_4 y z w b u)))))))))+((-1)*(d4_23_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_20_4,d0_21_4,d0_22_3,d0_22_4,d0_23_3,d0_23_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_4_4,d2_5_3,d2_5_4,d2_6_2,d2_6_3,d2_6_4,d2_7_1,d2_7_2,d2_7_3,d2_8_0,d2_8_1,d2_8_2,d2_9_0,d2_9_1,d3_13_4,d3_14_3,d3_14_4,d3_15_2,d3_15_3,d3_15_4,d3_16_1,d3_16_2,d3_16_3,d3_17_0,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_23_4]
  ring
#print axioms coefficient_23_4
compact_certificate_declaration theorem coefficient_23_5 (y z w b u : ℂ) :
    (innerCertificate23 y z w b u)[5]?=some 0 := by
  change some (((((((d0_20_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_21_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_22_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_22_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_23_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_23_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_4_5 y z w b u)*(d3_19_0 y z w b u))+0)+((((d2_5_4 y z w b u)*(d3_18_1 y z w b u))+(((d2_5_5 y z w b u)*(d3_18_0 y z w b u))+0))+((((d2_6_3 y z w b u)*(d3_17_2 y z w b u))+((d2_6_4 y z w b u)*(d3_17_1 y z w b u)))+((((d2_7_2 y z w b u)*(d3_16_3 y z w b u))+((d2_7_3 y z w b u)*(d3_16_2 y z w b u)))+((((d2_8_1 y z w b u)*(d3_15_4 y z w b u))+((d2_8_2 y z w b u)*(d3_15_3 y z w b u)))+(((d2_9_1 y z w b u)*(d3_14_4 y z w b u))+((d2_10_0 y z w b u)*(d3_13_5 y z w b u)))))))))+((-1)*(d4_23_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_20_5,d0_21_5,d0_22_4,d0_22_5,d0_23_4,d0_23_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_10_0,d2_4_5,d2_5_4,d2_5_5,d2_6_3,d2_6_4,d2_7_2,d2_7_3,d2_8_1,d2_8_2,d2_9_1,d3_13_5,d3_14_4,d3_15_3,d3_15_4,d3_16_2,d3_16_3,d3_17_1,d3_17_2,d3_18_0,d3_18_1,d3_19_0,d4_23_5]
  ring
#print axioms coefficient_23_5

compact_certificate_declaration theorem coefficient_23_6 (y z w b u : ℂ) :
    (innerCertificate23 y z w b u)[6]?=some 0 := by
  change some (((((((d0_20_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_21_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_22_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_22_6 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_23_5 y z w b u)*(d1_0_1 y z w b u)))))+(((d2_5_5 y z w b u)*(d3_18_1 y z w b u))+(((d2_6_4 y z w b u)*(d3_17_2 y z w b u))+(((d2_7_3 y z w b u)*(d3_16_3 y z w b u))+((d2_8_2 y z w b u)*(d3_15_4 y z w b u))))))+((-1)*(d4_23_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_20_6,d0_21_6,d0_22_5,d0_22_6,d0_23_5,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_5_5,d2_6_4,d2_7_3,d2_8_2,d3_15_4,d3_16_3,d3_17_2,d3_18_1,d4_23_6]
  ring
#print axioms coefficient_23_6
compact_certificate_declaration theorem coefficient_23_7 (y z w b u : ℂ) :
    (innerCertificate23 y z w b u)[7]?=some 0 := by
  change some ((((((d0_20_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_21_7 y z w b u)*(d1_2_0 y z w b u))+0)+((d0_22_6 y z w b u)*(d1_1_1 y z w b u))))+((-1)*(d4_23_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_20_7,d0_21_7,d0_22_6,d1_1_1,d1_2_0,d1_3_0,d4_23_7]
  ring
#print axioms coefficient_23_7
compact_certificate_declaration theorem coefficient_23_8 (y z w b u : ℂ) :
    (innerCertificate23 y z w b u)[8]?=some 0 := by
  change some (((((d0_20_8 y z w b u)*(d1_3_0 y z w b u))+0)+((-1)*(d4_23_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_20_8,d1_3_0,d4_23_8]
  ring
#print axioms coefficient_23_8

end SmallLevelTwentySixMMPPariTrace026
end

end

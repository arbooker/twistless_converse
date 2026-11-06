module
public import SmallLevelTwentySixMMPPariTraceTwentyFourV4
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
compact_certificate_declaration theorem certificate_length (y z w a b u : ℂ) : (certificate y z w a b u).length=32 := by
  norm_num [certificate,add,multiply,scale,coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6]

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
compact_certificate_declaration theorem inner_length_0 (y z w b u : ℂ) : (innerCertificate0 y z w b u).length=14 := by
  norm_num [innerCertificate0,add,multiply,scale,inner0_0,inner1_0,inner2_0,inner3_0,inner4_0]
compact_certificate_declaration theorem inner_eval_0 (y z w a b u : ℂ) :
    evaluate a (innerCertificate0 y z w b u)=(((((c0_0 y z w a b u)*(c1_0 y z w a b u))+0)+(((c2_0 y z w a b u)*(c3_0 y z w a b u))+0))+((-1)*(c4_0 y z w a b u))) := by
  simp only [innerCertificate0,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_0,c1_0,c2_0,c3_0,c4_0]
#print axioms inner_eval_0

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

compact_certificate_declaration theorem coefficient_0_0 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[0]?=some 0 := by
  change some ((((((d0_0_0 y z w b u)*(d1_0_0 y z w b u))+0)+(((d2_0_0 y z w b u)*(d3_0_0 y z w b u))+0))+0))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d1_0_0,d2_0_0,d3_0_0]
  ring
#print axioms coefficient_0_0
compact_certificate_declaration theorem coefficient_0_1 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[1]?=some 0 := by
  change some (((((d0_0_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_0_1 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_0 y z w b u)*(d3_0_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_0_0 y z w b u))+0))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d1_0_0,d1_0_1,d2_0_0,d2_0_1,d3_0_0,d3_0_1]
  ring
#print axioms coefficient_0_1
compact_certificate_declaration theorem coefficient_0_2 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[2]?=some 0 := by
  change some (((((d0_0_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_0_2 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_0 y z w b u)*(d3_0_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_0_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_0_0 y z w b u))+0)))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_1,d0_0_2,d1_0_0,d1_0_1,d2_0_0,d2_0_1,d2_0_2,d3_0_0,d3_0_1,d3_0_2]
  ring
#print axioms coefficient_0_2

compact_certificate_declaration theorem coefficient_0_3 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[3]?=some 0 := by
  change some (((((d0_0_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_0_3 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_0 y z w b u)*(d3_0_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_0_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_0_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_0_0 y z w b u))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_2,d0_0_3,d1_0_0,d1_0_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d3_0_0,d3_0_1,d3_0_2,d3_0_3]
  ring
#print axioms coefficient_0_3
compact_certificate_declaration theorem coefficient_0_4 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[4]?=some 0 := by
  change some (((((d0_0_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_0_4 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_0 y z w b u)*(d3_0_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_0_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_0_2 y z w b u))+(((d2_0_3 y z w b u)*(d3_0_1 y z w b u))+(((d2_0_4 y z w b u)*(d3_0_0 y z w b u))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_3,d0_0_4,d1_0_0,d1_0_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_0_4]
  ring
#print axioms coefficient_0_4
compact_certificate_declaration theorem coefficient_0_5 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[5]?=some 0 := by
  change some (((((d0_0_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_0_5 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_0 y z w b u)*(d3_0_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_0_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_0_3 y z w b u))+(((d2_0_3 y z w b u)*(d3_0_2 y z w b u))+(((d2_0_4 y z w b u)*(d3_0_1 y z w b u))+(((d2_0_5 y z w b u)*(d3_0_0 y z w b u))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_4,d0_0_5,d1_0_0,d1_0_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_0_5]
  ring
#print axioms coefficient_0_5

compact_certificate_declaration theorem coefficient_0_6 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[6]?=some 0 := by
  change some (((((d0_0_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_0_6 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_0 y z w b u)*(d3_0_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_0_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_0_4 y z w b u))+(((d2_0_3 y z w b u)*(d3_0_3 y z w b u))+(((d2_0_4 y z w b u)*(d3_0_2 y z w b u))+((d2_0_5 y z w b u)*(d3_0_1 y z w b u)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_5,d0_0_6,d1_0_0,d1_0_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_0_6]
  ring
#print axioms coefficient_0_6
compact_certificate_declaration theorem coefficient_0_7 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[7]?=some 0 := by
  change some (((((d0_0_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_0_7 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_0 y z w b u)*(d3_0_7 y z w b u))+(((d2_0_1 y z w b u)*(d3_0_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_0_5 y z w b u))+(((d2_0_3 y z w b u)*(d3_0_4 y z w b u))+(((d2_0_4 y z w b u)*(d3_0_3 y z w b u))+((d2_0_5 y z w b u)*(d3_0_2 y z w b u)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_6,d0_0_7,d1_0_0,d1_0_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_0_7]
  ring
#print axioms coefficient_0_7
compact_certificate_declaration theorem coefficient_0_8 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[8]?=some 0 := by
  change some (((((d0_0_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_0_8 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_0 y z w b u)*(d3_0_8 y z w b u))+(((d2_0_1 y z w b u)*(d3_0_7 y z w b u))+(((d2_0_2 y z w b u)*(d3_0_6 y z w b u))+(((d2_0_3 y z w b u)*(d3_0_5 y z w b u))+(((d2_0_4 y z w b u)*(d3_0_4 y z w b u))+((d2_0_5 y z w b u)*(d3_0_3 y z w b u)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_7,d0_0_8,d1_0_0,d1_0_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_0_8]
  ring
#print axioms coefficient_0_8

compact_certificate_declaration theorem coefficient_0_9 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[9]?=some 0 := by
  change some (((((d0_0_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_0_9 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_1 y z w b u)*(d3_0_8 y z w b u))+(((d2_0_2 y z w b u)*(d3_0_7 y z w b u))+(((d2_0_3 y z w b u)*(d3_0_6 y z w b u))+(((d2_0_4 y z w b u)*(d3_0_5 y z w b u))+((d2_0_5 y z w b u)*(d3_0_4 y z w b u))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_8,d0_0_9,d1_0_0,d1_0_1,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_0_8]
  ring
#print axioms coefficient_0_9
compact_certificate_declaration theorem coefficient_0_10 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[10]?=some 0 := by
  change some (((((d0_0_9 y z w b u)*(d1_0_1 y z w b u))+(((d0_0_10 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_2 y z w b u)*(d3_0_8 y z w b u))+(((d2_0_3 y z w b u)*(d3_0_7 y z w b u))+(((d2_0_4 y z w b u)*(d3_0_6 y z w b u))+((d2_0_5 y z w b u)*(d3_0_5 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_10,d0_0_9,d1_0_0,d1_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d3_0_5,d3_0_6,d3_0_7,d3_0_8]
  ring
#print axioms coefficient_0_10
compact_certificate_declaration theorem coefficient_0_11 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[11]?=some 0 := by
  change some (((((d0_0_10 y z w b u)*(d1_0_1 y z w b u))+(((d0_0_11 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_3 y z w b u)*(d3_0_8 y z w b u))+(((d2_0_4 y z w b u)*(d3_0_7 y z w b u))+((d2_0_5 y z w b u)*(d3_0_6 y z w b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_10,d0_0_11,d1_0_0,d1_0_1,d2_0_3,d2_0_4,d2_0_5,d3_0_6,d3_0_7,d3_0_8]
  ring
#print axioms coefficient_0_11

compact_certificate_declaration theorem coefficient_0_12 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[12]?=some 0 := by
  change some (((((d0_0_11 y z w b u)*(d1_0_1 y z w b u))+(((d0_0_12 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_4 y z w b u)*(d3_0_8 y z w b u))+((d2_0_5 y z w b u)*(d3_0_7 y z w b u)))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_11,d0_0_12,d1_0_0,d1_0_1,d2_0_4,d2_0_5,d3_0_7,d3_0_8]
  ring
#print axioms coefficient_0_12
compact_certificate_declaration theorem coefficient_0_13 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[13]?=some 0 := by
  change some ((((d0_0_12 y z w b u)*(d1_0_1 y z w b u))+((d2_0_5 y z w b u)*(d3_0_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_12,d1_0_1,d2_0_5,d3_0_8]
  ring
#print axioms coefficient_0_13

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
compact_certificate_declaration theorem inner_length_1 (y z w b u : ℂ) : (innerCertificate1 y z w b u).length=15 := by
  norm_num [innerCertificate1,add,multiply,scale,inner0_0,inner0_1,inner1_0,inner1_1,inner2_0,inner2_1,inner3_0,inner3_1,inner4_1]
compact_certificate_declaration theorem inner_eval_1 (y z w a b u : ℂ) :
    evaluate a (innerCertificate1 y z w b u)=(((((c0_0 y z w a b u)*(c1_1 y z w a b u))+(((c0_1 y z w a b u)*(c1_0 y z w a b u))+0))+(((c2_0 y z w a b u)*(c3_1 y z w a b u))+(((c2_1 y z w a b u)*(c3_0 y z w a b u))+0)))+((-1)*(c4_1 y z w a b u))) := by
  simp only [innerCertificate1,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_0,c0_1,c1_0,c1_1,c2_0,c2_1,c3_0,c3_1,c4_1]
#print axioms inner_eval_1

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

compact_certificate_declaration theorem coefficient_1_0 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[0]?=some 0 := by
  change some (((((((d0_0_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_1_0 y z w b u)*(d1_0_0 y z w b u))+0))+((((d2_0_0 y z w b u)*(d3_1_0 y z w b u))+0)+(((d2_1_0 y z w b u)*(d3_0_0 y z w b u))+0)))+0))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_1_0,d1_0_0,d1_1_0,d2_0_0,d2_1_0,d3_0_0,d3_1_0]
  ring
#print axioms coefficient_1_0
compact_certificate_declaration theorem coefficient_1_1 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[1]?=some 0 := by
  change some ((((((d0_0_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_0_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_1_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_1 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_0 y z w b u)*(d3_1_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_1_0 y z w b u))+0))+(((d2_1_0 y z w b u)*(d3_0_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_0_0 y z w b u))+0)))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d3_0_0,d3_0_1,d3_1_0,d3_1_1]
  ring
#print axioms coefficient_1_1
compact_certificate_declaration theorem coefficient_1_2 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[2]?=some 0 := by
  change some ((((((d0_0_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_0_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_1_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_2 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_0 y z w b u)*(d3_1_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_1_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_1_0 y z w b u))+0)))+(((d2_1_0 y z w b u)*(d3_0_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_0_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_0_0 y z w b u))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_1,d0_0_2,d0_1_1,d0_1_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d3_0_0,d3_0_1,d3_0_2,d3_1_0,d3_1_1,d3_1_2]
  ring
#print axioms coefficient_1_2

compact_certificate_declaration theorem coefficient_1_3 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[3]?=some 0 := by
  change some ((((((d0_0_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_0_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_1_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_3 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_0 y z w b u)*(d3_1_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_1_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_1_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_1_0 y z w b u))+0))))+(((d2_1_0 y z w b u)*(d3_0_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_0_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_0_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_0_0 y z w b u))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_2,d0_0_3,d0_1_2,d0_1_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_1_0,d3_1_1,d3_1_2,d3_1_3]
  ring
#print axioms coefficient_1_3
compact_certificate_declaration theorem coefficient_1_4 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[4]?=some 0 := by
  change some ((((((d0_0_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_0_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_1_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_4 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_0 y z w b u)*(d3_1_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_1_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_1_2 y z w b u))+(((d2_0_3 y z w b u)*(d3_1_1 y z w b u))+(((d2_0_4 y z w b u)*(d3_1_0 y z w b u))+0)))))+(((d2_1_0 y z w b u)*(d3_0_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_0_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_0_2 y z w b u))+(((d2_1_3 y z w b u)*(d3_0_1 y z w b u))+(((d2_1_4 y z w b u)*(d3_0_0 y z w b u))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_3,d0_0_4,d0_1_3,d0_1_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_1_4]
  ring
#print axioms coefficient_1_4
compact_certificate_declaration theorem coefficient_1_5 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[5]?=some 0 := by
  change some ((((((d0_0_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_0_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_1_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_5 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_0 y z w b u)*(d3_1_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_1_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_1_3 y z w b u))+(((d2_0_3 y z w b u)*(d3_1_2 y z w b u))+(((d2_0_4 y z w b u)*(d3_1_1 y z w b u))+(((d2_0_5 y z w b u)*(d3_1_0 y z w b u))+0))))))+(((d2_1_0 y z w b u)*(d3_0_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_0_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_0_3 y z w b u))+(((d2_1_3 y z w b u)*(d3_0_2 y z w b u))+(((d2_1_4 y z w b u)*(d3_0_1 y z w b u))+(((d2_1_5 y z w b u)*(d3_0_0 y z w b u))+0)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_4,d0_0_5,d0_1_4,d0_1_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_1_5]
  ring
#print axioms coefficient_1_5

compact_certificate_declaration theorem coefficient_1_6 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[6]?=some 0 := by
  change some ((((((d0_0_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_0_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_1_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_6 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_0 y z w b u)*(d3_1_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_1_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_1_4 y z w b u))+(((d2_0_3 y z w b u)*(d3_1_3 y z w b u))+(((d2_0_4 y z w b u)*(d3_1_2 y z w b u))+((d2_0_5 y z w b u)*(d3_1_1 y z w b u)))))))+(((d2_1_0 y z w b u)*(d3_0_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_0_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_0_4 y z w b u))+(((d2_1_3 y z w b u)*(d3_0_3 y z w b u))+(((d2_1_4 y z w b u)*(d3_0_2 y z w b u))+((d2_1_5 y z w b u)*(d3_0_1 y z w b u))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_5,d0_0_6,d0_1_5,d0_1_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_1_6]
  ring
#print axioms coefficient_1_6
compact_certificate_declaration theorem coefficient_1_7 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[7]?=some 0 := by
  change some ((((((d0_0_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_0_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_1_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_7 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_0 y z w b u)*(d3_1_7 y z w b u))+(((d2_0_1 y z w b u)*(d3_1_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_1_5 y z w b u))+(((d2_0_3 y z w b u)*(d3_1_4 y z w b u))+(((d2_0_4 y z w b u)*(d3_1_3 y z w b u))+((d2_0_5 y z w b u)*(d3_1_2 y z w b u)))))))+(((d2_1_0 y z w b u)*(d3_0_7 y z w b u))+(((d2_1_1 y z w b u)*(d3_0_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_0_5 y z w b u))+(((d2_1_3 y z w b u)*(d3_0_4 y z w b u))+(((d2_1_4 y z w b u)*(d3_0_3 y z w b u))+((d2_1_5 y z w b u)*(d3_0_2 y z w b u))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_6,d0_0_7,d0_1_6,d0_1_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_1_7]
  ring
#print axioms coefficient_1_7
compact_certificate_declaration theorem coefficient_1_8 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[8]?=some 0 := by
  change some ((((((d0_0_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_0_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_1_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_8 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_0 y z w b u)*(d3_1_8 y z w b u))+(((d2_0_1 y z w b u)*(d3_1_7 y z w b u))+(((d2_0_2 y z w b u)*(d3_1_6 y z w b u))+(((d2_0_3 y z w b u)*(d3_1_5 y z w b u))+(((d2_0_4 y z w b u)*(d3_1_4 y z w b u))+((d2_0_5 y z w b u)*(d3_1_3 y z w b u)))))))+(((d2_1_0 y z w b u)*(d3_0_8 y z w b u))+(((d2_1_1 y z w b u)*(d3_0_7 y z w b u))+(((d2_1_2 y z w b u)*(d3_0_6 y z w b u))+(((d2_1_3 y z w b u)*(d3_0_5 y z w b u))+(((d2_1_4 y z w b u)*(d3_0_4 y z w b u))+((d2_1_5 y z w b u)*(d3_0_3 y z w b u))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_7,d0_0_8,d0_1_7,d0_1_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_1_8]
  ring
#print axioms coefficient_1_8

compact_certificate_declaration theorem coefficient_1_9 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[9]?=some 0 := by
  change some ((((((d0_0_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_0_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_1_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_9 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_0 y z w b u)*(d3_1_9 y z w b u))+(((d2_0_1 y z w b u)*(d3_1_8 y z w b u))+(((d2_0_2 y z w b u)*(d3_1_7 y z w b u))+(((d2_0_3 y z w b u)*(d3_1_6 y z w b u))+(((d2_0_4 y z w b u)*(d3_1_5 y z w b u))+((d2_0_5 y z w b u)*(d3_1_4 y z w b u)))))))+(((d2_1_1 y z w b u)*(d3_0_8 y z w b u))+(((d2_1_2 y z w b u)*(d3_0_7 y z w b u))+(((d2_1_3 y z w b u)*(d3_0_6 y z w b u))+(((d2_1_4 y z w b u)*(d3_0_5 y z w b u))+((d2_1_5 y z w b u)*(d3_0_4 y z w b u)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_8,d0_0_9,d0_1_8,d0_1_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_1_9]
  ring
#print axioms coefficient_1_9
compact_certificate_declaration theorem coefficient_1_10 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[10]?=some 0 := by
  change some ((((((d0_0_9 y z w b u)*(d1_1_1 y z w b u))+(((d0_0_10 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_1_9 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_10 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_1 y z w b u)*(d3_1_9 y z w b u))+(((d2_0_2 y z w b u)*(d3_1_8 y z w b u))+(((d2_0_3 y z w b u)*(d3_1_7 y z w b u))+(((d2_0_4 y z w b u)*(d3_1_6 y z w b u))+((d2_0_5 y z w b u)*(d3_1_5 y z w b u))))))+(((d2_1_2 y z w b u)*(d3_0_8 y z w b u))+(((d2_1_3 y z w b u)*(d3_0_7 y z w b u))+(((d2_1_4 y z w b u)*(d3_0_6 y z w b u))+((d2_1_5 y z w b u)*(d3_0_5 y z w b u))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_10,d0_0_9,d0_1_10,d0_1_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_1_9]
  ring
#print axioms coefficient_1_10
compact_certificate_declaration theorem coefficient_1_11 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[11]?=some 0 := by
  change some ((((((d0_0_10 y z w b u)*(d1_1_1 y z w b u))+(((d0_0_11 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_1_10 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_11 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_2 y z w b u)*(d3_1_9 y z w b u))+(((d2_0_3 y z w b u)*(d3_1_8 y z w b u))+(((d2_0_4 y z w b u)*(d3_1_7 y z w b u))+((d2_0_5 y z w b u)*(d3_1_6 y z w b u)))))+(((d2_1_3 y z w b u)*(d3_0_8 y z w b u))+(((d2_1_4 y z w b u)*(d3_0_7 y z w b u))+((d2_1_5 y z w b u)*(d3_0_6 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_10,d0_0_11,d0_1_10,d0_1_11,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_3,d2_1_4,d2_1_5,d3_0_6,d3_0_7,d3_0_8,d3_1_6,d3_1_7,d3_1_8,d3_1_9]
  ring
#print axioms coefficient_1_11

compact_certificate_declaration theorem coefficient_1_12 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[12]?=some 0 := by
  change some ((((((d0_0_11 y z w b u)*(d1_1_1 y z w b u))+(((d0_0_12 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_1_11 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_12 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_3 y z w b u)*(d3_1_9 y z w b u))+(((d2_0_4 y z w b u)*(d3_1_8 y z w b u))+((d2_0_5 y z w b u)*(d3_1_7 y z w b u))))+(((d2_1_4 y z w b u)*(d3_0_8 y z w b u))+((d2_1_5 y z w b u)*(d3_0_7 y z w b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_11,d0_0_12,d0_1_11,d0_1_12,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_3,d2_0_4,d2_0_5,d2_1_4,d2_1_5,d3_0_7,d3_0_8,d3_1_7,d3_1_8,d3_1_9]
  ring
#print axioms coefficient_1_12
compact_certificate_declaration theorem coefficient_1_13 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[13]?=some 0 := by
  change some (((((d0_0_12 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_12 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_13 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_4 y z w b u)*(d3_1_9 y z w b u))+((d2_0_5 y z w b u)*(d3_1_8 y z w b u)))+((d2_1_5 y z w b u)*(d3_0_8 y z w b u)))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_12,d0_1_12,d0_1_13,d1_0_0,d1_0_1,d1_1_1,d2_0_4,d2_0_5,d2_1_5,d3_0_8,d3_1_8,d3_1_9]
  ring
#print axioms coefficient_1_13
compact_certificate_declaration theorem coefficient_1_14 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[14]?=some 0 := by
  change some ((((d0_1_13 y z w b u)*(d1_0_1 y z w b u))+((d2_0_5 y z w b u)*(d3_1_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_13,d1_0_1,d2_0_5,d3_1_9]
  ring
#print axioms coefficient_1_14

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
compact_certificate_declaration theorem inner_length_2 (y z w b u : ℂ) : (innerCertificate2 y z w b u).length=15 := by
  norm_num [innerCertificate2,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner1_0,inner1_1,inner1_2,inner2_0,inner2_1,inner2_2,inner3_0,inner3_1,inner3_2,inner4_2]
compact_certificate_declaration theorem inner_eval_2 (y z w a b u : ℂ) :
    evaluate a (innerCertificate2 y z w b u)=(((((c0_0 y z w a b u)*(c1_2 y z w a b u))+(((c0_1 y z w a b u)*(c1_1 y z w a b u))+(((c0_2 y z w a b u)*(c1_0 y z w a b u))+0)))+(((c2_0 y z w a b u)*(c3_2 y z w a b u))+(((c2_1 y z w a b u)*(c3_1 y z w a b u))+(((c2_2 y z w a b u)*(c3_0 y z w a b u))+0))))+((-1)*(c4_2 y z w a b u))) := by
  simp only [innerCertificate2,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_0,c0_1,c0_2,c1_0,c1_1,c1_2,c2_0,c2_1,c2_2,c3_0,c3_1,c3_2,c4_2]
#print axioms inner_eval_2

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

compact_certificate_declaration theorem coefficient_2_0 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[0]?=some 0 := by
  change some (((((((d0_0_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_2_0 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_0 y z w b u)*(d3_2_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_1_0 y z w b u))+0)+(((d2_2_0 y z w b u)*(d3_0_0 y z w b u))+0))))+0))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_1_0,d0_2_0,d1_0_0,d1_1_0,d1_2_0,d2_0_0,d2_1_0,d2_2_0,d3_0_0,d3_1_0,d3_2_0]
  ring
#print axioms coefficient_2_0
compact_certificate_declaration theorem coefficient_2_1 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[1]?=some 0 := by
  change some ((((((d0_0_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_1 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_2_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_2_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_1_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_1_0 y z w b u))+0))+(((d2_2_0 y z w b u)*(d3_0_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_0_0 y z w b u))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d3_0_0,d3_0_1,d3_1_0,d3_1_1,d3_2_0,d3_2_1]
  ring
#print axioms coefficient_2_1
compact_certificate_declaration theorem coefficient_2_2 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[2]?=some 0 := by
  change some ((((((d0_0_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_2 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_2_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_2_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_2_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_1_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_1_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_1_0 y z w b u))+0)))+(((d2_2_0 y z w b u)*(d3_0_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_0_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_0_0 y z w b u))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_2,d0_1_1,d0_1_2,d0_2_1,d0_2_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d3_0_0,d3_0_1,d3_0_2,d3_1_0,d3_1_1,d3_1_2,d3_2_0,d3_2_1,d3_2_2]
  ring
#print axioms coefficient_2_2

compact_certificate_declaration theorem coefficient_2_3 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[3]?=some 0 := by
  change some ((((((d0_0_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_3 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_2_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_2_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_2_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_2_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_1_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_1_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_1_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_1_0 y z w b u))+0))))+(((d2_2_0 y z w b u)*(d3_0_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_0_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_0_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_0_0 y z w b u))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_3,d0_1_2,d0_1_3,d0_2_2,d0_2_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_2_0,d3_2_1,d3_2_2,d3_2_3]
  ring
#print axioms coefficient_2_3
compact_certificate_declaration theorem coefficient_2_4 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[4]?=some 0 := by
  change some ((((((d0_0_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_4 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_2_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_2_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_2_2 y z w b u))+(((d2_0_3 y z w b u)*(d3_2_1 y z w b u))+(((d2_0_4 y z w b u)*(d3_2_0 y z w b u))+0)))))+((((d2_1_0 y z w b u)*(d3_1_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_1_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_1_2 y z w b u))+(((d2_1_3 y z w b u)*(d3_1_1 y z w b u))+(((d2_1_4 y z w b u)*(d3_1_0 y z w b u))+0)))))+(((d2_2_0 y z w b u)*(d3_0_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_0_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_0_2 y z w b u))+(((d2_2_3 y z w b u)*(d3_0_1 y z w b u))+(((d2_2_4 y z w b u)*(d3_0_0 y z w b u))+0)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_4,d0_1_3,d0_1_4,d0_2_3,d0_2_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_2_4]
  ring
#print axioms coefficient_2_4
compact_certificate_declaration theorem coefficient_2_5 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[5]?=some 0 := by
  change some ((((((d0_0_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_5 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_2_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_2_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_2_3 y z w b u))+(((d2_0_3 y z w b u)*(d3_2_2 y z w b u))+(((d2_0_4 y z w b u)*(d3_2_1 y z w b u))+(((d2_0_5 y z w b u)*(d3_2_0 y z w b u))+0))))))+((((d2_1_0 y z w b u)*(d3_1_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_1_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_1_3 y z w b u))+(((d2_1_3 y z w b u)*(d3_1_2 y z w b u))+(((d2_1_4 y z w b u)*(d3_1_1 y z w b u))+(((d2_1_5 y z w b u)*(d3_1_0 y z w b u))+0))))))+(((d2_2_0 y z w b u)*(d3_0_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_0_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_0_3 y z w b u))+(((d2_2_3 y z w b u)*(d3_0_2 y z w b u))+(((d2_2_4 y z w b u)*(d3_0_1 y z w b u))+(((d2_2_5 y z w b u)*(d3_0_0 y z w b u))+0))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_5,d0_1_4,d0_1_5,d0_2_4,d0_2_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_2_5]
  ring
#print axioms coefficient_2_5

compact_certificate_declaration theorem coefficient_2_6 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[6]?=some 0 := by
  change some ((((((d0_0_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_6 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_2_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_2_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_2_4 y z w b u))+(((d2_0_3 y z w b u)*(d3_2_3 y z w b u))+(((d2_0_4 y z w b u)*(d3_2_2 y z w b u))+((d2_0_5 y z w b u)*(d3_2_1 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_1_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_1_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_1_4 y z w b u))+(((d2_1_3 y z w b u)*(d3_1_3 y z w b u))+(((d2_1_4 y z w b u)*(d3_1_2 y z w b u))+((d2_1_5 y z w b u)*(d3_1_1 y z w b u)))))))+(((d2_2_0 y z w b u)*(d3_0_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_0_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_0_4 y z w b u))+(((d2_2_3 y z w b u)*(d3_0_3 y z w b u))+(((d2_2_4 y z w b u)*(d3_0_2 y z w b u))+((d2_2_5 y z w b u)*(d3_0_1 y z w b u)))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_6,d0_1_5,d0_1_6,d0_2_5,d0_2_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_2_6]
  ring
#print axioms coefficient_2_6
compact_certificate_declaration theorem coefficient_2_7 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[7]?=some 0 := by
  change some ((((((d0_0_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_7 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_2_7 y z w b u))+(((d2_0_1 y z w b u)*(d3_2_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_2_5 y z w b u))+(((d2_0_3 y z w b u)*(d3_2_4 y z w b u))+(((d2_0_4 y z w b u)*(d3_2_3 y z w b u))+((d2_0_5 y z w b u)*(d3_2_2 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_1_7 y z w b u))+(((d2_1_1 y z w b u)*(d3_1_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_1_5 y z w b u))+(((d2_1_3 y z w b u)*(d3_1_4 y z w b u))+(((d2_1_4 y z w b u)*(d3_1_3 y z w b u))+((d2_1_5 y z w b u)*(d3_1_2 y z w b u)))))))+(((d2_2_0 y z w b u)*(d3_0_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_0_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_0_5 y z w b u))+(((d2_2_3 y z w b u)*(d3_0_4 y z w b u))+(((d2_2_4 y z w b u)*(d3_0_3 y z w b u))+((d2_2_5 y z w b u)*(d3_0_2 y z w b u)))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_7,d0_1_6,d0_1_7,d0_2_6,d0_2_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_2_7]
  ring
#print axioms coefficient_2_7
compact_certificate_declaration theorem coefficient_2_8 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[8]?=some 0 := by
  change some ((((((d0_0_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_8 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_2_8 y z w b u))+(((d2_0_1 y z w b u)*(d3_2_7 y z w b u))+(((d2_0_2 y z w b u)*(d3_2_6 y z w b u))+(((d2_0_3 y z w b u)*(d3_2_5 y z w b u))+(((d2_0_4 y z w b u)*(d3_2_4 y z w b u))+((d2_0_5 y z w b u)*(d3_2_3 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_1_8 y z w b u))+(((d2_1_1 y z w b u)*(d3_1_7 y z w b u))+(((d2_1_2 y z w b u)*(d3_1_6 y z w b u))+(((d2_1_3 y z w b u)*(d3_1_5 y z w b u))+(((d2_1_4 y z w b u)*(d3_1_4 y z w b u))+((d2_1_5 y z w b u)*(d3_1_3 y z w b u)))))))+(((d2_2_0 y z w b u)*(d3_0_8 y z w b u))+(((d2_2_1 y z w b u)*(d3_0_7 y z w b u))+(((d2_2_2 y z w b u)*(d3_0_6 y z w b u))+(((d2_2_3 y z w b u)*(d3_0_5 y z w b u))+(((d2_2_4 y z w b u)*(d3_0_4 y z w b u))+((d2_2_5 y z w b u)*(d3_0_3 y z w b u)))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_8,d0_1_7,d0_1_8,d0_2_7,d0_2_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_2_8]
  ring
#print axioms coefficient_2_8

compact_certificate_declaration theorem coefficient_2_9 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[9]?=some 0 := by
  change some ((((((d0_0_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_9 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_2_9 y z w b u))+(((d2_0_1 y z w b u)*(d3_2_8 y z w b u))+(((d2_0_2 y z w b u)*(d3_2_7 y z w b u))+(((d2_0_3 y z w b u)*(d3_2_6 y z w b u))+(((d2_0_4 y z w b u)*(d3_2_5 y z w b u))+((d2_0_5 y z w b u)*(d3_2_4 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_1_9 y z w b u))+(((d2_1_1 y z w b u)*(d3_1_8 y z w b u))+(((d2_1_2 y z w b u)*(d3_1_7 y z w b u))+(((d2_1_3 y z w b u)*(d3_1_6 y z w b u))+(((d2_1_4 y z w b u)*(d3_1_5 y z w b u))+((d2_1_5 y z w b u)*(d3_1_4 y z w b u)))))))+(((d2_2_1 y z w b u)*(d3_0_8 y z w b u))+(((d2_2_2 y z w b u)*(d3_0_7 y z w b u))+(((d2_2_3 y z w b u)*(d3_0_6 y z w b u))+(((d2_2_4 y z w b u)*(d3_0_5 y z w b u))+((d2_2_5 y z w b u)*(d3_0_4 y z w b u))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_9,d0_1_8,d0_1_9,d0_2_8,d0_2_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_1_9,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_2_9]
  ring
#print axioms coefficient_2_9
compact_certificate_declaration theorem coefficient_2_10 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[10]?=some 0 := by
  change some ((((((d0_0_10 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_9 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_10 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_9 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_10 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_1 y z w b u)*(d3_2_9 y z w b u))+(((d2_0_2 y z w b u)*(d3_2_8 y z w b u))+(((d2_0_3 y z w b u)*(d3_2_7 y z w b u))+(((d2_0_4 y z w b u)*(d3_2_6 y z w b u))+((d2_0_5 y z w b u)*(d3_2_5 y z w b u))))))+((((d2_1_1 y z w b u)*(d3_1_9 y z w b u))+(((d2_1_2 y z w b u)*(d3_1_8 y z w b u))+(((d2_1_3 y z w b u)*(d3_1_7 y z w b u))+(((d2_1_4 y z w b u)*(d3_1_6 y z w b u))+((d2_1_5 y z w b u)*(d3_1_5 y z w b u))))))+(((d2_2_2 y z w b u)*(d3_0_8 y z w b u))+(((d2_2_3 y z w b u)*(d3_0_7 y z w b u))+(((d2_2_4 y z w b u)*(d3_0_6 y z w b u))+((d2_2_5 y z w b u)*(d3_0_5 y z w b u)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_10,d0_1_10,d0_1_9,d0_2_10,d0_2_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_1_9,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_2_9]
  ring
#print axioms coefficient_2_10
compact_certificate_declaration theorem coefficient_2_11 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[11]?=some 0 := by
  change some ((((((d0_0_11 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_10 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_11 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_10 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_11 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_2 y z w b u)*(d3_2_9 y z w b u))+(((d2_0_3 y z w b u)*(d3_2_8 y z w b u))+(((d2_0_4 y z w b u)*(d3_2_7 y z w b u))+((d2_0_5 y z w b u)*(d3_2_6 y z w b u)))))+((((d2_1_2 y z w b u)*(d3_1_9 y z w b u))+(((d2_1_3 y z w b u)*(d3_1_8 y z w b u))+(((d2_1_4 y z w b u)*(d3_1_7 y z w b u))+((d2_1_5 y z w b u)*(d3_1_6 y z w b u)))))+(((d2_2_3 y z w b u)*(d3_0_8 y z w b u))+(((d2_2_4 y z w b u)*(d3_0_7 y z w b u))+((d2_2_5 y z w b u)*(d3_0_6 y z w b u))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_11,d0_1_10,d0_1_11,d0_2_10,d0_2_11,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_3,d2_2_4,d2_2_5,d3_0_6,d3_0_7,d3_0_8,d3_1_6,d3_1_7,d3_1_8,d3_1_9,d3_2_6,d3_2_7,d3_2_8,d3_2_9]
  ring
#print axioms coefficient_2_11

compact_certificate_declaration theorem coefficient_2_12 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[12]?=some 0 := by
  change some ((((((d0_0_12 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_11 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_12 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_11 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_12 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_3 y z w b u)*(d3_2_9 y z w b u))+(((d2_0_4 y z w b u)*(d3_2_8 y z w b u))+((d2_0_5 y z w b u)*(d3_2_7 y z w b u))))+((((d2_1_3 y z w b u)*(d3_1_9 y z w b u))+(((d2_1_4 y z w b u)*(d3_1_8 y z w b u))+((d2_1_5 y z w b u)*(d3_1_7 y z w b u))))+(((d2_2_4 y z w b u)*(d3_0_8 y z w b u))+((d2_2_5 y z w b u)*(d3_0_7 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_12,d0_1_11,d0_1_12,d0_2_11,d0_2_12,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_3,d2_0_4,d2_0_5,d2_1_3,d2_1_4,d2_1_5,d2_2_4,d2_2_5,d3_0_7,d3_0_8,d3_1_7,d3_1_8,d3_1_9,d3_2_7,d3_2_8,d3_2_9]
  ring
#print axioms coefficient_2_12
compact_certificate_declaration theorem coefficient_2_13 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[13]?=some 0 := by
  change some ((((((d0_1_12 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_13 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_12 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_13 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_4 y z w b u)*(d3_2_9 y z w b u))+((d2_0_5 y z w b u)*(d3_2_8 y z w b u)))+((((d2_1_4 y z w b u)*(d3_1_9 y z w b u))+((d2_1_5 y z w b u)*(d3_1_8 y z w b u)))+((d2_2_5 y z w b u)*(d3_0_8 y z w b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_12,d0_1_13,d0_2_12,d0_2_13,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_4,d2_0_5,d2_1_4,d2_1_5,d2_2_5,d3_0_8,d3_1_8,d3_1_9,d3_2_8,d3_2_9]
  ring
#print axioms coefficient_2_13
compact_certificate_declaration theorem coefficient_2_14 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[14]?=some 0 := by
  change some (((((d0_1_13 y z w b u)*(d1_1_1 y z w b u))+((d0_2_13 y z w b u)*(d1_0_1 y z w b u)))+(((d2_0_5 y z w b u)*(d3_2_9 y z w b u))+((d2_1_5 y z w b u)*(d3_1_9 y z w b u)))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_13,d0_2_13,d1_0_1,d1_1_1,d2_0_5,d2_1_5,d3_1_9,d3_2_9]
  ring
#print axioms coefficient_2_14

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
compact_certificate_declaration theorem inner_length_3 (y z w b u : ℂ) : (innerCertificate3 y z w b u).length=15 := by
  norm_num [innerCertificate3,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner0_3,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner3_0,inner3_1,inner3_2,inner3_3,inner4_3]
compact_certificate_declaration theorem inner_eval_3 (y z w a b u : ℂ) :
    evaluate a (innerCertificate3 y z w b u)=(((((c0_0 y z w a b u)*(c1_3 y z w a b u))+(((c0_1 y z w a b u)*(c1_2 y z w a b u))+(((c0_2 y z w a b u)*(c1_1 y z w a b u))+(((c0_3 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_3 y z w a b u))+(((c2_1 y z w a b u)*(c3_2 y z w a b u))+(((c2_2 y z w a b u)*(c3_1 y z w a b u))+(((c2_3 y z w a b u)*(c3_0 y z w a b u))+0)))))+((-1)*(c4_3 y z w a b u))) := by
  simp only [innerCertificate3,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_0,c0_1,c0_2,c0_3,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c3_0,c3_1,c3_2,c3_3,c4_3]
#print axioms inner_eval_3

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

compact_certificate_declaration theorem coefficient_3_0 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[0]?=some 0 := by
  change some (((((((d0_0_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_3_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_3_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_2_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_1_0 y z w b u))+0)+(((d2_3_0 y z w b u)*(d3_0_0 y z w b u))+0)))))+0))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_1_0,d0_2_0,d0_3_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_1_0,d2_2_0,d2_3_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0]
  ring
#print axioms coefficient_3_0
compact_certificate_declaration theorem coefficient_3_1 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[1]?=some 0 := by
  change some ((((((d0_0_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_3_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_3_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_2_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_2_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_1_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_0 y z w b u))+0))+(((d2_3_0 y z w b u)*(d3_0_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_0_0 y z w b u))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_1,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d0_3_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d3_0_0,d3_0_1,d3_1_0,d3_1_1,d3_2_0,d3_2_1,d3_3_0,d3_3_1]
  ring
#print axioms coefficient_3_1
compact_certificate_declaration theorem coefficient_3_2 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[2]?=some 0 := by
  change some ((((((d0_0_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_3_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_3_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_3_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_2_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_2_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_2_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_1_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_0 y z w b u))+0)))+(((d2_3_0 y z w b u)*(d3_0_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_0_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_0_0 y z w b u))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_2,d0_1_2,d0_2_1,d0_2_2,d0_3_1,d0_3_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d3_0_0,d3_0_1,d3_0_2,d3_1_0,d3_1_1,d3_1_2,d3_2_0,d3_2_1,d3_2_2,d3_3_0,d3_3_1,d3_3_2]
  ring
#print axioms coefficient_3_2

compact_certificate_declaration theorem coefficient_3_3 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[3]?=some 0 := by
  change some ((((((d0_0_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_3_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_3_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_3_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_3_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_2_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_2_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_2_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_2_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_1_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_1_0 y z w b u))+0))))+(((d2_3_0 y z w b u)*(d3_0_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_0_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_0_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_0_0 y z w b u))+0)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_3,d0_1_3,d0_2_2,d0_2_3,d0_3_2,d0_3_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_3_0,d3_3_1,d3_3_2,d3_3_3]
  ring
#print axioms coefficient_3_3
compact_certificate_declaration theorem coefficient_3_4 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[4]?=some 0 := by
  change some ((((((d0_0_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_3_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_3_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_3_2 y z w b u))+(((d2_0_3 y z w b u)*(d3_3_1 y z w b u))+(((d2_0_4 y z w b u)*(d3_3_0 y z w b u))+0)))))+((((d2_1_0 y z w b u)*(d3_2_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_2_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_2_2 y z w b u))+(((d2_1_3 y z w b u)*(d3_2_1 y z w b u))+(((d2_1_4 y z w b u)*(d3_2_0 y z w b u))+0)))))+((((d2_2_0 y z w b u)*(d3_1_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_2 y z w b u))+(((d2_2_3 y z w b u)*(d3_1_1 y z w b u))+(((d2_2_4 y z w b u)*(d3_1_0 y z w b u))+0)))))+(((d2_3_0 y z w b u)*(d3_0_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_0_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_0_2 y z w b u))+(((d2_3_3 y z w b u)*(d3_0_1 y z w b u))+(((d2_3_4 y z w b u)*(d3_0_0 y z w b u))+0))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_4,d0_1_4,d0_2_3,d0_2_4,d0_3_3,d0_3_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d3_3_4]
  ring
#print axioms coefficient_3_4

compact_certificate_declaration theorem coefficient_3_5 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[5]?=some 0 := by
  change some ((((((d0_0_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_3_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_3_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_3_3 y z w b u))+(((d2_0_3 y z w b u)*(d3_3_2 y z w b u))+(((d2_0_4 y z w b u)*(d3_3_1 y z w b u))+(((d2_0_5 y z w b u)*(d3_3_0 y z w b u))+0))))))+((((d2_1_0 y z w b u)*(d3_2_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_2_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_2_3 y z w b u))+(((d2_1_3 y z w b u)*(d3_2_2 y z w b u))+(((d2_1_4 y z w b u)*(d3_2_1 y z w b u))+(((d2_1_5 y z w b u)*(d3_2_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_1_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_3 y z w b u))+(((d2_2_3 y z w b u)*(d3_1_2 y z w b u))+(((d2_2_4 y z w b u)*(d3_1_1 y z w b u))+(((d2_2_5 y z w b u)*(d3_1_0 y z w b u))+0))))))+(((d2_3_0 y z w b u)*(d3_0_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_0_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_0_3 y z w b u))+(((d2_3_3 y z w b u)*(d3_0_2 y z w b u))+(((d2_3_4 y z w b u)*(d3_0_1 y z w b u))+(((d2_3_5 y z w b u)*(d3_0_0 y z w b u))+0)))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_5,d0_1_5,d0_2_4,d0_2_5,d0_3_4,d0_3_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d3_3_5]
  ring
#print axioms coefficient_3_5
compact_certificate_declaration theorem coefficient_3_6 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[6]?=some 0 := by
  change some ((((((d0_0_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_3_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_3_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_3_4 y z w b u))+(((d2_0_3 y z w b u)*(d3_3_3 y z w b u))+(((d2_0_4 y z w b u)*(d3_3_2 y z w b u))+((d2_0_5 y z w b u)*(d3_3_1 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_2_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_2_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_2_4 y z w b u))+(((d2_1_3 y z w b u)*(d3_2_3 y z w b u))+(((d2_1_4 y z w b u)*(d3_2_2 y z w b u))+((d2_1_5 y z w b u)*(d3_2_1 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_1_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_4 y z w b u))+(((d2_2_3 y z w b u)*(d3_1_3 y z w b u))+(((d2_2_4 y z w b u)*(d3_1_2 y z w b u))+((d2_2_5 y z w b u)*(d3_1_1 y z w b u)))))))+(((d2_3_0 y z w b u)*(d3_0_6 y z w b u))+(((d2_3_1 y z w b u)*(d3_0_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_0_4 y z w b u))+(((d2_3_3 y z w b u)*(d3_0_3 y z w b u))+(((d2_3_4 y z w b u)*(d3_0_2 y z w b u))+((d2_3_5 y z w b u)*(d3_0_1 y z w b u))))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_6,d0_1_6,d0_2_5,d0_2_6,d0_3_5,d0_3_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d3_3_6]
  ring
#print axioms coefficient_3_6

compact_certificate_declaration theorem coefficient_3_7 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[7]?=some 0 := by
  change some ((((((d0_0_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_3_7 y z w b u))+(((d2_0_1 y z w b u)*(d3_3_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_3_5 y z w b u))+(((d2_0_3 y z w b u)*(d3_3_4 y z w b u))+(((d2_0_4 y z w b u)*(d3_3_3 y z w b u))+((d2_0_5 y z w b u)*(d3_3_2 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_2_7 y z w b u))+(((d2_1_1 y z w b u)*(d3_2_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_2_5 y z w b u))+(((d2_1_3 y z w b u)*(d3_2_4 y z w b u))+(((d2_1_4 y z w b u)*(d3_2_3 y z w b u))+((d2_1_5 y z w b u)*(d3_2_2 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_1_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_5 y z w b u))+(((d2_2_3 y z w b u)*(d3_1_4 y z w b u))+(((d2_2_4 y z w b u)*(d3_1_3 y z w b u))+((d2_2_5 y z w b u)*(d3_1_2 y z w b u)))))))+(((d2_3_0 y z w b u)*(d3_0_7 y z w b u))+(((d2_3_1 y z w b u)*(d3_0_6 y z w b u))+(((d2_3_2 y z w b u)*(d3_0_5 y z w b u))+(((d2_3_3 y z w b u)*(d3_0_4 y z w b u))+(((d2_3_4 y z w b u)*(d3_0_3 y z w b u))+((d2_3_5 y z w b u)*(d3_0_2 y z w b u))))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_7,d0_1_7,d0_2_6,d0_2_7,d0_3_6,d0_3_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d3_3_7]
  ring
#print axioms coefficient_3_7
compact_certificate_declaration theorem coefficient_3_8 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[8]?=some 0 := by
  change some ((((((d0_0_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_3_8 y z w b u))+(((d2_0_1 y z w b u)*(d3_3_7 y z w b u))+(((d2_0_2 y z w b u)*(d3_3_6 y z w b u))+(((d2_0_3 y z w b u)*(d3_3_5 y z w b u))+(((d2_0_4 y z w b u)*(d3_3_4 y z w b u))+((d2_0_5 y z w b u)*(d3_3_3 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_2_8 y z w b u))+(((d2_1_1 y z w b u)*(d3_2_7 y z w b u))+(((d2_1_2 y z w b u)*(d3_2_6 y z w b u))+(((d2_1_3 y z w b u)*(d3_2_5 y z w b u))+(((d2_1_4 y z w b u)*(d3_2_4 y z w b u))+((d2_1_5 y z w b u)*(d3_2_3 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_1_8 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_7 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_6 y z w b u))+(((d2_2_3 y z w b u)*(d3_1_5 y z w b u))+(((d2_2_4 y z w b u)*(d3_1_4 y z w b u))+((d2_2_5 y z w b u)*(d3_1_3 y z w b u)))))))+(((d2_3_0 y z w b u)*(d3_0_8 y z w b u))+(((d2_3_1 y z w b u)*(d3_0_7 y z w b u))+(((d2_3_2 y z w b u)*(d3_0_6 y z w b u))+(((d2_3_3 y z w b u)*(d3_0_5 y z w b u))+(((d2_3_4 y z w b u)*(d3_0_4 y z w b u))+((d2_3_5 y z w b u)*(d3_0_3 y z w b u))))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_8,d0_1_8,d0_2_7,d0_2_8,d0_3_7,d0_3_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d3_3_8]
  ring
#print axioms coefficient_3_8
compact_certificate_declaration theorem coefficient_3_9 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[9]?=some 0 := by
  change some ((((((d0_0_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_9 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_3_9 y z w b u))+(((d2_0_1 y z w b u)*(d3_3_8 y z w b u))+(((d2_0_2 y z w b u)*(d3_3_7 y z w b u))+(((d2_0_3 y z w b u)*(d3_3_6 y z w b u))+(((d2_0_4 y z w b u)*(d3_3_5 y z w b u))+((d2_0_5 y z w b u)*(d3_3_4 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_2_9 y z w b u))+(((d2_1_1 y z w b u)*(d3_2_8 y z w b u))+(((d2_1_2 y z w b u)*(d3_2_7 y z w b u))+(((d2_1_3 y z w b u)*(d3_2_6 y z w b u))+(((d2_1_4 y z w b u)*(d3_2_5 y z w b u))+((d2_1_5 y z w b u)*(d3_2_4 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_1_9 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_8 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_7 y z w b u))+(((d2_2_3 y z w b u)*(d3_1_6 y z w b u))+(((d2_2_4 y z w b u)*(d3_1_5 y z w b u))+((d2_2_5 y z w b u)*(d3_1_4 y z w b u)))))))+(((d2_3_1 y z w b u)*(d3_0_8 y z w b u))+(((d2_3_2 y z w b u)*(d3_0_7 y z w b u))+(((d2_3_3 y z w b u)*(d3_0_6 y z w b u))+(((d2_3_4 y z w b u)*(d3_0_5 y z w b u))+((d2_3_5 y z w b u)*(d3_0_4 y z w b u)))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_9,d0_1_9,d0_2_8,d0_2_9,d0_3_8,d0_3_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_1_9,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_2_9,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d3_3_8,d3_3_9]
  ring
#print axioms coefficient_3_9

compact_certificate_declaration theorem coefficient_3_10 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[10]?=some 0 := by
  change some ((((((d0_0_10 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_10 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_9 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_10 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_9 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_10 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_3_9 y z w b u))+(((d2_0_2 y z w b u)*(d3_3_8 y z w b u))+(((d2_0_3 y z w b u)*(d3_3_7 y z w b u))+(((d2_0_4 y z w b u)*(d3_3_6 y z w b u))+((d2_0_5 y z w b u)*(d3_3_5 y z w b u))))))+((((d2_1_1 y z w b u)*(d3_2_9 y z w b u))+(((d2_1_2 y z w b u)*(d3_2_8 y z w b u))+(((d2_1_3 y z w b u)*(d3_2_7 y z w b u))+(((d2_1_4 y z w b u)*(d3_2_6 y z w b u))+((d2_1_5 y z w b u)*(d3_2_5 y z w b u))))))+((((d2_2_1 y z w b u)*(d3_1_9 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_8 y z w b u))+(((d2_2_3 y z w b u)*(d3_1_7 y z w b u))+(((d2_2_4 y z w b u)*(d3_1_6 y z w b u))+((d2_2_5 y z w b u)*(d3_1_5 y z w b u))))))+(((d2_3_2 y z w b u)*(d3_0_8 y z w b u))+(((d2_3_3 y z w b u)*(d3_0_7 y z w b u))+(((d2_3_4 y z w b u)*(d3_0_6 y z w b u))+((d2_3_5 y z w b u)*(d3_0_5 y z w b u))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_10,d0_1_10,d0_2_10,d0_2_9,d0_3_10,d0_3_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_1_9,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_2_9,d3_3_5,d3_3_6,d3_3_7,d3_3_8,d3_3_9]
  ring
#print axioms coefficient_3_10
compact_certificate_declaration theorem coefficient_3_11 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[11]?=some 0 := by
  change some ((((((d0_0_11 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_11 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_10 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_11 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_10 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_11 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_3_9 y z w b u))+(((d2_0_3 y z w b u)*(d3_3_8 y z w b u))+(((d2_0_4 y z w b u)*(d3_3_7 y z w b u))+((d2_0_5 y z w b u)*(d3_3_6 y z w b u)))))+((((d2_1_2 y z w b u)*(d3_2_9 y z w b u))+(((d2_1_3 y z w b u)*(d3_2_8 y z w b u))+(((d2_1_4 y z w b u)*(d3_2_7 y z w b u))+((d2_1_5 y z w b u)*(d3_2_6 y z w b u)))))+((((d2_2_2 y z w b u)*(d3_1_9 y z w b u))+(((d2_2_3 y z w b u)*(d3_1_8 y z w b u))+(((d2_2_4 y z w b u)*(d3_1_7 y z w b u))+((d2_2_5 y z w b u)*(d3_1_6 y z w b u)))))+(((d2_3_3 y z w b u)*(d3_0_8 y z w b u))+(((d2_3_4 y z w b u)*(d3_0_7 y z w b u))+((d2_3_5 y z w b u)*(d3_0_6 y z w b u)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_11,d0_1_11,d0_2_10,d0_2_11,d0_3_10,d0_3_11,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_3,d2_3_4,d2_3_5,d3_0_6,d3_0_7,d3_0_8,d3_1_6,d3_1_7,d3_1_8,d3_1_9,d3_2_6,d3_2_7,d3_2_8,d3_2_9,d3_3_6,d3_3_7,d3_3_8,d3_3_9]
  ring
#print axioms coefficient_3_11
compact_certificate_declaration theorem coefficient_3_12 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[12]?=some 0 := by
  change some ((((((d0_0_12 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_12 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_11 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_12 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_11 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_12 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_3 y z w b u)*(d3_3_9 y z w b u))+(((d2_0_4 y z w b u)*(d3_3_8 y z w b u))+((d2_0_5 y z w b u)*(d3_3_7 y z w b u))))+((((d2_1_3 y z w b u)*(d3_2_9 y z w b u))+(((d2_1_4 y z w b u)*(d3_2_8 y z w b u))+((d2_1_5 y z w b u)*(d3_2_7 y z w b u))))+((((d2_2_3 y z w b u)*(d3_1_9 y z w b u))+(((d2_2_4 y z w b u)*(d3_1_8 y z w b u))+((d2_2_5 y z w b u)*(d3_1_7 y z w b u))))+(((d2_3_4 y z w b u)*(d3_0_8 y z w b u))+((d2_3_5 y z w b u)*(d3_0_7 y z w b u))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_12,d0_1_12,d0_2_11,d0_2_12,d0_3_11,d0_3_12,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_0_4,d2_0_5,d2_1_3,d2_1_4,d2_1_5,d2_2_3,d2_2_4,d2_2_5,d2_3_4,d2_3_5,d3_0_7,d3_0_8,d3_1_7,d3_1_8,d3_1_9,d3_2_7,d3_2_8,d3_2_9,d3_3_7,d3_3_8,d3_3_9]
  ring
#print axioms coefficient_3_12

compact_certificate_declaration theorem coefficient_3_13 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[13]?=some 0 := by
  change some ((((((d0_1_13 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_12 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_13 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_12 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_13 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_4 y z w b u)*(d3_3_9 y z w b u))+((d2_0_5 y z w b u)*(d3_3_8 y z w b u)))+((((d2_1_4 y z w b u)*(d3_2_9 y z w b u))+((d2_1_5 y z w b u)*(d3_2_8 y z w b u)))+((((d2_2_4 y z w b u)*(d3_1_9 y z w b u))+((d2_2_5 y z w b u)*(d3_1_8 y z w b u)))+((d2_3_5 y z w b u)*(d3_0_8 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_13,d0_2_12,d0_2_13,d0_3_12,d0_3_13,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_4,d2_0_5,d2_1_4,d2_1_5,d2_2_4,d2_2_5,d2_3_5,d3_0_8,d3_1_8,d3_1_9,d3_2_8,d3_2_9,d3_3_8,d3_3_9]
  ring
#print axioms coefficient_3_13
compact_certificate_declaration theorem coefficient_3_14 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[14]?=some 0 := by
  change some (((((d0_2_13 y z w b u)*(d1_1_1 y z w b u))+((d0_3_13 y z w b u)*(d1_0_1 y z w b u)))+(((d2_0_5 y z w b u)*(d3_3_9 y z w b u))+(((d2_1_5 y z w b u)*(d3_2_9 y z w b u))+((d2_2_5 y z w b u)*(d3_1_9 y z w b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_13,d0_3_13,d1_0_1,d1_1_1,d2_0_5,d2_1_5,d2_2_5,d3_1_9,d3_2_9,d3_3_9]
  ring
#print axioms coefficient_3_14

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
compact_certificate_declaration theorem inner_length_4 (y z w b u : ℂ) : (innerCertificate4 y z w b u).length=15 := by
  norm_num [innerCertificate4,add,multiply,scale,inner0_1,inner0_2,inner0_3,inner0_4,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner4_4]
compact_certificate_declaration theorem inner_eval_4 (y z w a b u : ℂ) :
    evaluate a (innerCertificate4 y z w b u)=(((((c0_1 y z w a b u)*(c1_3 y z w a b u))+(((c0_2 y z w a b u)*(c1_2 y z w a b u))+(((c0_3 y z w a b u)*(c1_1 y z w a b u))+(((c0_4 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_4 y z w a b u))+(((c2_1 y z w a b u)*(c3_3 y z w a b u))+(((c2_2 y z w a b u)*(c3_2 y z w a b u))+(((c2_3 y z w a b u)*(c3_1 y z w a b u))+(((c2_4 y z w a b u)*(c3_0 y z w a b u))+0))))))+((-1)*(c4_4 y z w a b u))) := by
  simp only [innerCertificate4,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_1,c0_2,c0_3,c0_4,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c3_0,c3_1,c3_2,c3_3,c3_4,c4_4]
#print axioms inner_eval_4

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

compact_certificate_declaration theorem coefficient_4_0 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[0]?=some 0 := by
  change some (((((((d0_1_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_4_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_4_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_3_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_2_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_1_0 y z w b u))+0)+(((d2_4_0 y z w b u)*(d3_0_0 y z w b u))+0))))))+(((-1)*(d4_4_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_0,d0_2_0,d0_3_0,d0_4_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d4_4_0]
  ring
#print axioms coefficient_4_0
compact_certificate_declaration theorem coefficient_4_1 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[1]?=some 0 := by
  change some (((((((d0_1_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_4_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_4_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_3_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_3_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_2_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_1_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_1_0 y z w b u))+0))+(((d2_4_0 y z w b u)*(d3_0_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_0_0 y z w b u))+0)))))))+((-1)*(d4_4_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_1,d0_2_1,d0_3_0,d0_3_1,d0_4_0,d0_4_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d3_0_0,d3_0_1,d3_1_0,d3_1_1,d3_2_0,d3_2_1,d3_3_0,d3_3_1,d3_4_0,d3_4_1,d4_4_1]
  ring
#print axioms coefficient_4_1
compact_certificate_declaration theorem coefficient_4_2 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[2]?=some 0 := by
  change some (((((((d0_1_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_4_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_4_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_4_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_3_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_3_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_3_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_2_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_2_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_1_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_1_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_1_0 y z w b u))+0)))+(((d2_4_0 y z w b u)*(d3_0_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_0_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_0_0 y z w b u))+0))))))))+((-1)*(d4_4_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_2,d0_2_2,d0_3_1,d0_3_2,d0_4_1,d0_4_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d3_0_0,d3_0_1,d3_0_2,d3_1_0,d3_1_1,d3_1_2,d3_2_0,d3_2_1,d3_2_2,d3_3_0,d3_3_1,d3_3_2,d3_4_0,d3_4_1,d3_4_2,d4_4_2]
  ring
#print axioms coefficient_4_2

compact_certificate_declaration theorem coefficient_4_3 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[3]?=some 0 := by
  change some (((((((d0_1_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_4_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_4_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_4_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_4_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_3_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_3_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_3_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_3_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_2_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_2_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_2_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_1_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_1_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_1_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_1_0 y z w b u))+0))))+(((d2_4_0 y z w b u)*(d3_0_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_0_2 y z w b u))+(((d2_4_2 y z w b u)*(d3_0_1 y z w b u))+(((d2_4_3 y z w b u)*(d3_0_0 y z w b u))+0)))))))))+((-1)*(d4_4_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_3,d0_2_3,d0_3_2,d0_3_3,d0_4_2,d0_4_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d3_4_0,d3_4_1,d3_4_2,d3_4_3,d4_4_3]
  ring
#print axioms coefficient_4_3
compact_certificate_declaration theorem coefficient_4_4 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[4]?=some 0 := by
  change some (((((((d0_1_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_4_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_4_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_4_2 y z w b u))+(((d2_0_3 y z w b u)*(d3_4_1 y z w b u))+(((d2_0_4 y z w b u)*(d3_4_0 y z w b u))+0)))))+((((d2_1_0 y z w b u)*(d3_3_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_3_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_3_2 y z w b u))+(((d2_1_3 y z w b u)*(d3_3_1 y z w b u))+(((d2_1_4 y z w b u)*(d3_3_0 y z w b u))+0)))))+((((d2_2_0 y z w b u)*(d3_2_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_2_2 y z w b u))+(((d2_2_3 y z w b u)*(d3_2_1 y z w b u))+(((d2_2_4 y z w b u)*(d3_2_0 y z w b u))+0)))))+((((d2_3_0 y z w b u)*(d3_1_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_1_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_1_2 y z w b u))+(((d2_3_3 y z w b u)*(d3_1_1 y z w b u))+(((d2_3_4 y z w b u)*(d3_1_0 y z w b u))+0)))))+(((d2_4_0 y z w b u)*(d3_0_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_0_3 y z w b u))+(((d2_4_2 y z w b u)*(d3_0_2 y z w b u))+(((d2_4_3 y z w b u)*(d3_0_1 y z w b u))+(((d2_4_4 y z w b u)*(d3_0_0 y z w b u))+0))))))))))+((-1)*(d4_4_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_4,d0_2_4,d0_3_3,d0_3_4,d0_4_3,d0_4_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d3_4_0,d3_4_1,d3_4_2,d3_4_3,d3_4_4,d4_4_4]
  ring
#print axioms coefficient_4_4

compact_certificate_declaration theorem coefficient_4_5 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[5]?=some 0 := by
  change some (((((((d0_1_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_4_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_4_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_4_3 y z w b u))+(((d2_0_3 y z w b u)*(d3_4_2 y z w b u))+(((d2_0_4 y z w b u)*(d3_4_1 y z w b u))+(((d2_0_5 y z w b u)*(d3_4_0 y z w b u))+0))))))+((((d2_1_0 y z w b u)*(d3_3_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_3_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_3_3 y z w b u))+(((d2_1_3 y z w b u)*(d3_3_2 y z w b u))+(((d2_1_4 y z w b u)*(d3_3_1 y z w b u))+(((d2_1_5 y z w b u)*(d3_3_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_2_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_2_3 y z w b u))+(((d2_2_3 y z w b u)*(d3_2_2 y z w b u))+(((d2_2_4 y z w b u)*(d3_2_1 y z w b u))+(((d2_2_5 y z w b u)*(d3_2_0 y z w b u))+0))))))+((((d2_3_0 y z w b u)*(d3_1_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_1_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_1_3 y z w b u))+(((d2_3_3 y z w b u)*(d3_1_2 y z w b u))+(((d2_3_4 y z w b u)*(d3_1_1 y z w b u))+(((d2_3_5 y z w b u)*(d3_1_0 y z w b u))+0))))))+(((d2_4_0 y z w b u)*(d3_0_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_0_4 y z w b u))+(((d2_4_2 y z w b u)*(d3_0_3 y z w b u))+(((d2_4_3 y z w b u)*(d3_0_2 y z w b u))+(((d2_4_4 y z w b u)*(d3_0_1 y z w b u))+(((d2_4_5 y z w b u)*(d3_0_0 y z w b u))+0)))))))))))+((-1)*(d4_4_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_5,d0_2_5,d0_3_4,d0_3_5,d0_4_4,d0_4_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d3_4_0,d3_4_1,d3_4_2,d3_4_3,d3_4_4,d3_4_5,d4_4_5]
  ring
#print axioms coefficient_4_5
compact_certificate_declaration theorem coefficient_4_6 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[6]?=some 0 := by
  change some (((((((d0_1_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_4_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_4_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_4_4 y z w b u))+(((d2_0_3 y z w b u)*(d3_4_3 y z w b u))+(((d2_0_4 y z w b u)*(d3_4_2 y z w b u))+((d2_0_5 y z w b u)*(d3_4_1 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_3_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_3_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_3_4 y z w b u))+(((d2_1_3 y z w b u)*(d3_3_3 y z w b u))+(((d2_1_4 y z w b u)*(d3_3_2 y z w b u))+((d2_1_5 y z w b u)*(d3_3_1 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_2_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_2_4 y z w b u))+(((d2_2_3 y z w b u)*(d3_2_3 y z w b u))+(((d2_2_4 y z w b u)*(d3_2_2 y z w b u))+((d2_2_5 y z w b u)*(d3_2_1 y z w b u)))))))+((((d2_3_0 y z w b u)*(d3_1_6 y z w b u))+(((d2_3_1 y z w b u)*(d3_1_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_1_4 y z w b u))+(((d2_3_3 y z w b u)*(d3_1_3 y z w b u))+(((d2_3_4 y z w b u)*(d3_1_2 y z w b u))+((d2_3_5 y z w b u)*(d3_1_1 y z w b u)))))))+(((d2_4_0 y z w b u)*(d3_0_6 y z w b u))+(((d2_4_1 y z w b u)*(d3_0_5 y z w b u))+(((d2_4_2 y z w b u)*(d3_0_4 y z w b u))+(((d2_4_3 y z w b u)*(d3_0_3 y z w b u))+(((d2_4_4 y z w b u)*(d3_0_2 y z w b u))+((d2_4_5 y z w b u)*(d3_0_1 y z w b u))))))))))))+((-1)*(d4_4_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_6,d0_2_6,d0_3_5,d0_3_6,d0_4_5,d0_4_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d3_4_1,d3_4_2,d3_4_3,d3_4_4,d3_4_5,d3_4_6,d4_4_6]
  ring
#print axioms coefficient_4_6

compact_certificate_declaration theorem coefficient_4_7 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[7]?=some 0 := by
  change some (((((((d0_1_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_4_7 y z w b u))+(((d2_0_1 y z w b u)*(d3_4_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_4_5 y z w b u))+(((d2_0_3 y z w b u)*(d3_4_4 y z w b u))+(((d2_0_4 y z w b u)*(d3_4_3 y z w b u))+((d2_0_5 y z w b u)*(d3_4_2 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_3_7 y z w b u))+(((d2_1_1 y z w b u)*(d3_3_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_3_5 y z w b u))+(((d2_1_3 y z w b u)*(d3_3_4 y z w b u))+(((d2_1_4 y z w b u)*(d3_3_3 y z w b u))+((d2_1_5 y z w b u)*(d3_3_2 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_2_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_2_5 y z w b u))+(((d2_2_3 y z w b u)*(d3_2_4 y z w b u))+(((d2_2_4 y z w b u)*(d3_2_3 y z w b u))+((d2_2_5 y z w b u)*(d3_2_2 y z w b u)))))))+((((d2_3_0 y z w b u)*(d3_1_7 y z w b u))+(((d2_3_1 y z w b u)*(d3_1_6 y z w b u))+(((d2_3_2 y z w b u)*(d3_1_5 y z w b u))+(((d2_3_3 y z w b u)*(d3_1_4 y z w b u))+(((d2_3_4 y z w b u)*(d3_1_3 y z w b u))+((d2_3_5 y z w b u)*(d3_1_2 y z w b u)))))))+(((d2_4_0 y z w b u)*(d3_0_7 y z w b u))+(((d2_4_1 y z w b u)*(d3_0_6 y z w b u))+(((d2_4_2 y z w b u)*(d3_0_5 y z w b u))+(((d2_4_3 y z w b u)*(d3_0_4 y z w b u))+(((d2_4_4 y z w b u)*(d3_0_3 y z w b u))+((d2_4_5 y z w b u)*(d3_0_2 y z w b u))))))))))))+((-1)*(d4_4_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_7,d0_2_7,d0_3_6,d0_3_7,d0_4_6,d0_4_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d3_4_2,d3_4_3,d3_4_4,d3_4_5,d3_4_6,d3_4_7,d4_4_7]
  ring
#print axioms coefficient_4_7
compact_certificate_declaration theorem coefficient_4_8 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[8]?=some 0 := by
  change some (((((((d0_1_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_4_8 y z w b u))+(((d2_0_1 y z w b u)*(d3_4_7 y z w b u))+(((d2_0_2 y z w b u)*(d3_4_6 y z w b u))+(((d2_0_3 y z w b u)*(d3_4_5 y z w b u))+(((d2_0_4 y z w b u)*(d3_4_4 y z w b u))+((d2_0_5 y z w b u)*(d3_4_3 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_3_8 y z w b u))+(((d2_1_1 y z w b u)*(d3_3_7 y z w b u))+(((d2_1_2 y z w b u)*(d3_3_6 y z w b u))+(((d2_1_3 y z w b u)*(d3_3_5 y z w b u))+(((d2_1_4 y z w b u)*(d3_3_4 y z w b u))+((d2_1_5 y z w b u)*(d3_3_3 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_2_8 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_7 y z w b u))+(((d2_2_2 y z w b u)*(d3_2_6 y z w b u))+(((d2_2_3 y z w b u)*(d3_2_5 y z w b u))+(((d2_2_4 y z w b u)*(d3_2_4 y z w b u))+((d2_2_5 y z w b u)*(d3_2_3 y z w b u)))))))+((((d2_3_0 y z w b u)*(d3_1_8 y z w b u))+(((d2_3_1 y z w b u)*(d3_1_7 y z w b u))+(((d2_3_2 y z w b u)*(d3_1_6 y z w b u))+(((d2_3_3 y z w b u)*(d3_1_5 y z w b u))+(((d2_3_4 y z w b u)*(d3_1_4 y z w b u))+((d2_3_5 y z w b u)*(d3_1_3 y z w b u)))))))+(((d2_4_0 y z w b u)*(d3_0_8 y z w b u))+(((d2_4_1 y z w b u)*(d3_0_7 y z w b u))+(((d2_4_2 y z w b u)*(d3_0_6 y z w b u))+(((d2_4_3 y z w b u)*(d3_0_5 y z w b u))+(((d2_4_4 y z w b u)*(d3_0_4 y z w b u))+((d2_4_5 y z w b u)*(d3_0_3 y z w b u))))))))))))+((-1)*(d4_4_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_8,d0_2_8,d0_3_7,d0_3_8,d0_4_7,d0_4_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d3_3_8,d3_4_3,d3_4_4,d3_4_5,d3_4_6,d3_4_7,d3_4_8,d4_4_8]
  ring
#print axioms coefficient_4_8
compact_certificate_declaration theorem coefficient_4_9 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[9]?=some 0 := by
  change some (((((((d0_1_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_9 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_4_9 y z w b u))+(((d2_0_1 y z w b u)*(d3_4_8 y z w b u))+(((d2_0_2 y z w b u)*(d3_4_7 y z w b u))+(((d2_0_3 y z w b u)*(d3_4_6 y z w b u))+(((d2_0_4 y z w b u)*(d3_4_5 y z w b u))+((d2_0_5 y z w b u)*(d3_4_4 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_3_9 y z w b u))+(((d2_1_1 y z w b u)*(d3_3_8 y z w b u))+(((d2_1_2 y z w b u)*(d3_3_7 y z w b u))+(((d2_1_3 y z w b u)*(d3_3_6 y z w b u))+(((d2_1_4 y z w b u)*(d3_3_5 y z w b u))+((d2_1_5 y z w b u)*(d3_3_4 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_2_9 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_8 y z w b u))+(((d2_2_2 y z w b u)*(d3_2_7 y z w b u))+(((d2_2_3 y z w b u)*(d3_2_6 y z w b u))+(((d2_2_4 y z w b u)*(d3_2_5 y z w b u))+((d2_2_5 y z w b u)*(d3_2_4 y z w b u)))))))+((((d2_3_0 y z w b u)*(d3_1_9 y z w b u))+(((d2_3_1 y z w b u)*(d3_1_8 y z w b u))+(((d2_3_2 y z w b u)*(d3_1_7 y z w b u))+(((d2_3_3 y z w b u)*(d3_1_6 y z w b u))+(((d2_3_4 y z w b u)*(d3_1_5 y z w b u))+((d2_3_5 y z w b u)*(d3_1_4 y z w b u)))))))+(((d2_4_1 y z w b u)*(d3_0_8 y z w b u))+(((d2_4_2 y z w b u)*(d3_0_7 y z w b u))+(((d2_4_3 y z w b u)*(d3_0_6 y z w b u))+(((d2_4_4 y z w b u)*(d3_0_5 y z w b u))+((d2_4_5 y z w b u)*(d3_0_4 y z w b u)))))))))))+((-1)*(d4_4_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_9,d0_2_9,d0_3_8,d0_3_9,d0_4_8,d0_4_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_1_9,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_2_9,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d3_3_8,d3_3_9,d3_4_4,d3_4_5,d3_4_6,d3_4_7,d3_4_8,d3_4_9,d4_4_9]
  ring
#print axioms coefficient_4_9

compact_certificate_declaration theorem coefficient_4_10 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[10]?=some 0 := by
  change some ((((((d0_1_10 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_10 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_9 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_10 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_9 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_10 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_4_9 y z w b u))+(((d2_0_2 y z w b u)*(d3_4_8 y z w b u))+(((d2_0_3 y z w b u)*(d3_4_7 y z w b u))+(((d2_0_4 y z w b u)*(d3_4_6 y z w b u))+((d2_0_5 y z w b u)*(d3_4_5 y z w b u))))))+((((d2_1_1 y z w b u)*(d3_3_9 y z w b u))+(((d2_1_2 y z w b u)*(d3_3_8 y z w b u))+(((d2_1_3 y z w b u)*(d3_3_7 y z w b u))+(((d2_1_4 y z w b u)*(d3_3_6 y z w b u))+((d2_1_5 y z w b u)*(d3_3_5 y z w b u))))))+((((d2_2_1 y z w b u)*(d3_2_9 y z w b u))+(((d2_2_2 y z w b u)*(d3_2_8 y z w b u))+(((d2_2_3 y z w b u)*(d3_2_7 y z w b u))+(((d2_2_4 y z w b u)*(d3_2_6 y z w b u))+((d2_2_5 y z w b u)*(d3_2_5 y z w b u))))))+((((d2_3_1 y z w b u)*(d3_1_9 y z w b u))+(((d2_3_2 y z w b u)*(d3_1_8 y z w b u))+(((d2_3_3 y z w b u)*(d3_1_7 y z w b u))+(((d2_3_4 y z w b u)*(d3_1_6 y z w b u))+((d2_3_5 y z w b u)*(d3_1_5 y z w b u))))))+(((d2_4_2 y z w b u)*(d3_0_8 y z w b u))+(((d2_4_3 y z w b u)*(d3_0_7 y z w b u))+(((d2_4_4 y z w b u)*(d3_0_6 y z w b u))+((d2_4_5 y z w b u)*(d3_0_5 y z w b u)))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_10,d0_2_10,d0_3_10,d0_3_9,d0_4_10,d0_4_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_1_9,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_2_9,d3_3_5,d3_3_6,d3_3_7,d3_3_8,d3_3_9,d3_4_5,d3_4_6,d3_4_7,d3_4_8,d3_4_9]
  ring
#print axioms coefficient_4_10
compact_certificate_declaration theorem coefficient_4_11 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[11]?=some 0 := by
  change some ((((((d0_1_11 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_11 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_10 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_11 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_10 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_11 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_4_9 y z w b u))+(((d2_0_3 y z w b u)*(d3_4_8 y z w b u))+(((d2_0_4 y z w b u)*(d3_4_7 y z w b u))+((d2_0_5 y z w b u)*(d3_4_6 y z w b u)))))+((((d2_1_2 y z w b u)*(d3_3_9 y z w b u))+(((d2_1_3 y z w b u)*(d3_3_8 y z w b u))+(((d2_1_4 y z w b u)*(d3_3_7 y z w b u))+((d2_1_5 y z w b u)*(d3_3_6 y z w b u)))))+((((d2_2_2 y z w b u)*(d3_2_9 y z w b u))+(((d2_2_3 y z w b u)*(d3_2_8 y z w b u))+(((d2_2_4 y z w b u)*(d3_2_7 y z w b u))+((d2_2_5 y z w b u)*(d3_2_6 y z w b u)))))+((((d2_3_2 y z w b u)*(d3_1_9 y z w b u))+(((d2_3_3 y z w b u)*(d3_1_8 y z w b u))+(((d2_3_4 y z w b u)*(d3_1_7 y z w b u))+((d2_3_5 y z w b u)*(d3_1_6 y z w b u)))))+(((d2_4_3 y z w b u)*(d3_0_8 y z w b u))+(((d2_4_4 y z w b u)*(d3_0_7 y z w b u))+((d2_4_5 y z w b u)*(d3_0_6 y z w b u))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_11,d0_2_11,d0_3_10,d0_3_11,d0_4_10,d0_4_11,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_3,d2_4_4,d2_4_5,d3_0_6,d3_0_7,d3_0_8,d3_1_6,d3_1_7,d3_1_8,d3_1_9,d3_2_6,d3_2_7,d3_2_8,d3_2_9,d3_3_6,d3_3_7,d3_3_8,d3_3_9,d3_4_6,d3_4_7,d3_4_8,d3_4_9]
  ring
#print axioms coefficient_4_11
compact_certificate_declaration theorem coefficient_4_12 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[12]?=some 0 := by
  change some ((((((d0_1_12 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_12 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_11 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_12 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_11 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_12 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_3 y z w b u)*(d3_4_9 y z w b u))+(((d2_0_4 y z w b u)*(d3_4_8 y z w b u))+((d2_0_5 y z w b u)*(d3_4_7 y z w b u))))+((((d2_1_3 y z w b u)*(d3_3_9 y z w b u))+(((d2_1_4 y z w b u)*(d3_3_8 y z w b u))+((d2_1_5 y z w b u)*(d3_3_7 y z w b u))))+((((d2_2_3 y z w b u)*(d3_2_9 y z w b u))+(((d2_2_4 y z w b u)*(d3_2_8 y z w b u))+((d2_2_5 y z w b u)*(d3_2_7 y z w b u))))+((((d2_3_3 y z w b u)*(d3_1_9 y z w b u))+(((d2_3_4 y z w b u)*(d3_1_8 y z w b u))+((d2_3_5 y z w b u)*(d3_1_7 y z w b u))))+(((d2_4_4 y z w b u)*(d3_0_8 y z w b u))+((d2_4_5 y z w b u)*(d3_0_7 y z w b u)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_12,d0_2_12,d0_3_11,d0_3_12,d0_4_11,d0_4_12,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_0_4,d2_0_5,d2_1_3,d2_1_4,d2_1_5,d2_2_3,d2_2_4,d2_2_5,d2_3_3,d2_3_4,d2_3_5,d2_4_4,d2_4_5,d3_0_7,d3_0_8,d3_1_7,d3_1_8,d3_1_9,d3_2_7,d3_2_8,d3_2_9,d3_3_7,d3_3_8,d3_3_9,d3_4_7,d3_4_8,d3_4_9]
  ring
#print axioms coefficient_4_12

compact_certificate_declaration theorem coefficient_4_13 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[13]?=some 0 := by
  change some ((((((d0_1_13 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_13 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_12 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_13 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_12 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_13 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_4 y z w b u)*(d3_4_9 y z w b u))+((d2_0_5 y z w b u)*(d3_4_8 y z w b u)))+((((d2_1_4 y z w b u)*(d3_3_9 y z w b u))+((d2_1_5 y z w b u)*(d3_3_8 y z w b u)))+((((d2_2_4 y z w b u)*(d3_2_9 y z w b u))+((d2_2_5 y z w b u)*(d3_2_8 y z w b u)))+((((d2_3_4 y z w b u)*(d3_1_9 y z w b u))+((d2_3_5 y z w b u)*(d3_1_8 y z w b u)))+((d2_4_5 y z w b u)*(d3_0_8 y z w b u))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_13,d0_2_13,d0_3_12,d0_3_13,d0_4_12,d0_4_13,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_4,d2_0_5,d2_1_4,d2_1_5,d2_2_4,d2_2_5,d2_3_4,d2_3_5,d2_4_5,d3_0_8,d3_1_8,d3_1_9,d3_2_8,d3_2_9,d3_3_8,d3_3_9,d3_4_8,d3_4_9]
  ring
#print axioms coefficient_4_13
compact_certificate_declaration theorem coefficient_4_14 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[14]?=some 0 := by
  change some (((((d0_3_13 y z w b u)*(d1_1_1 y z w b u))+((d0_4_13 y z w b u)*(d1_0_1 y z w b u)))+(((d2_0_5 y z w b u)*(d3_4_9 y z w b u))+(((d2_1_5 y z w b u)*(d3_3_9 y z w b u))+(((d2_2_5 y z w b u)*(d3_2_9 y z w b u))+((d2_3_5 y z w b u)*(d3_1_9 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_13,d0_4_13,d1_0_1,d1_1_1,d2_0_5,d2_1_5,d2_2_5,d2_3_5,d3_1_9,d3_2_9,d3_3_9,d3_4_9]
  ring
#print axioms coefficient_4_14

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
compact_certificate_declaration theorem inner_length_5 (y z w b u : ℂ) : (innerCertificate5 y z w b u).length=15 := by
  norm_num [innerCertificate5,add,multiply,scale,inner0_2,inner0_3,inner0_4,inner0_5,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner4_5]
compact_certificate_declaration theorem inner_eval_5 (y z w a b u : ℂ) :
    evaluate a (innerCertificate5 y z w b u)=(((((c0_2 y z w a b u)*(c1_3 y z w a b u))+(((c0_3 y z w a b u)*(c1_2 y z w a b u))+(((c0_4 y z w a b u)*(c1_1 y z w a b u))+(((c0_5 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_5 y z w a b u))+(((c2_1 y z w a b u)*(c3_4 y z w a b u))+(((c2_2 y z w a b u)*(c3_3 y z w a b u))+(((c2_3 y z w a b u)*(c3_2 y z w a b u))+(((c2_4 y z w a b u)*(c3_1 y z w a b u))+(((c2_5 y z w a b u)*(c3_0 y z w a b u))+0)))))))+((-1)*(c4_5 y z w a b u))) := by
  simp only [innerCertificate5,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_2,c0_3,c0_4,c0_5,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c3_0,c3_1,c3_2,c3_3,c3_4,c3_5,c4_5]
#print axioms inner_eval_5

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

compact_certificate_declaration theorem coefficient_5_0 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[0]?=some 0 := by
  change some (((((((d0_2_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_5_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_5_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_4_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_3_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_2_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_1_0 y z w b u))+0)+(((d2_5_0 y z w b u)*(d3_0_0 y z w b u))+0)))))))+(((-1)*(d4_5_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_0,d0_3_0,d0_4_0,d0_5_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d4_5_0]
  ring
#print axioms coefficient_5_0
compact_certificate_declaration theorem coefficient_5_1 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[1]?=some 0 := by
  change some (((((((d0_2_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_5_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_5_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_4_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_4_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_3_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_2_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_2_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_1_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_1_0 y z w b u))+0))+(((d2_5_0 y z w b u)*(d3_0_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_0_0 y z w b u))+0))))))))+((-1)*(d4_5_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_1,d0_3_1,d0_4_0,d0_4_1,d0_5_0,d0_5_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d3_0_0,d3_0_1,d3_1_0,d3_1_1,d3_2_0,d3_2_1,d3_3_0,d3_3_1,d3_4_0,d3_4_1,d3_5_0,d3_5_1,d4_5_1]
  ring
#print axioms coefficient_5_1
compact_certificate_declaration theorem coefficient_5_2 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[2]?=some 0 := by
  change some (((((((d0_2_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_5_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_5_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_5_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_4_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_4_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_4_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_3_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_2_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_2_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_2_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_1_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_1_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_1_0 y z w b u))+0)))+(((d2_5_0 y z w b u)*(d3_0_2 y z w b u))+(((d2_5_1 y z w b u)*(d3_0_1 y z w b u))+(((d2_5_2 y z w b u)*(d3_0_0 y z w b u))+0)))))))))+((-1)*(d4_5_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_2,d0_3_2,d0_4_1,d0_4_2,d0_5_1,d0_5_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_5_2,d3_0_0,d3_0_1,d3_0_2,d3_1_0,d3_1_1,d3_1_2,d3_2_0,d3_2_1,d3_2_2,d3_3_0,d3_3_1,d3_3_2,d3_4_0,d3_4_1,d3_4_2,d3_5_0,d3_5_1,d3_5_2,d4_5_2]
  ring
#print axioms coefficient_5_2

compact_certificate_declaration theorem coefficient_5_3 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[3]?=some 0 := by
  change some (((((((d0_2_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_5_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_5_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_5_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_5_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_4_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_4_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_4_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_4_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_3_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_3_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_2_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_2_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_2_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_2_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_1_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_1_2 y z w b u))+(((d2_4_2 y z w b u)*(d3_1_1 y z w b u))+(((d2_4_3 y z w b u)*(d3_1_0 y z w b u))+0))))+(((d2_5_0 y z w b u)*(d3_0_3 y z w b u))+(((d2_5_1 y z w b u)*(d3_0_2 y z w b u))+(((d2_5_2 y z w b u)*(d3_0_1 y z w b u))+(((d2_5_3 y z w b u)*(d3_0_0 y z w b u))+0))))))))))+((-1)*(d4_5_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_3,d0_3_3,d0_4_2,d0_4_3,d0_5_2,d0_5_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d3_4_0,d3_4_1,d3_4_2,d3_4_3,d3_5_0,d3_5_1,d3_5_2,d3_5_3,d4_5_3]
  ring
#print axioms coefficient_5_3
compact_certificate_declaration theorem coefficient_5_4 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[4]?=some 0 := by
  change some (((((((d0_2_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_5_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_5_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_5_2 y z w b u))+(((d2_0_3 y z w b u)*(d3_5_1 y z w b u))+(((d2_0_4 y z w b u)*(d3_5_0 y z w b u))+0)))))+((((d2_1_0 y z w b u)*(d3_4_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_4_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_4_2 y z w b u))+(((d2_1_3 y z w b u)*(d3_4_1 y z w b u))+(((d2_1_4 y z w b u)*(d3_4_0 y z w b u))+0)))))+((((d2_2_0 y z w b u)*(d3_3_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_2 y z w b u))+(((d2_2_3 y z w b u)*(d3_3_1 y z w b u))+(((d2_2_4 y z w b u)*(d3_3_0 y z w b u))+0)))))+((((d2_3_0 y z w b u)*(d3_2_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_2_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_2_2 y z w b u))+(((d2_3_3 y z w b u)*(d3_2_1 y z w b u))+(((d2_3_4 y z w b u)*(d3_2_0 y z w b u))+0)))))+((((d2_4_0 y z w b u)*(d3_1_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_1_3 y z w b u))+(((d2_4_2 y z w b u)*(d3_1_2 y z w b u))+(((d2_4_3 y z w b u)*(d3_1_1 y z w b u))+(((d2_4_4 y z w b u)*(d3_1_0 y z w b u))+0)))))+(((d2_5_0 y z w b u)*(d3_0_4 y z w b u))+(((d2_5_1 y z w b u)*(d3_0_3 y z w b u))+(((d2_5_2 y z w b u)*(d3_0_2 y z w b u))+(((d2_5_3 y z w b u)*(d3_0_1 y z w b u))+(((d2_5_4 y z w b u)*(d3_0_0 y z w b u))+0)))))))))))+((-1)*(d4_5_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_4,d0_3_4,d0_4_3,d0_4_4,d0_5_3,d0_5_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d3_4_0,d3_4_1,d3_4_2,d3_4_3,d3_4_4,d3_5_0,d3_5_1,d3_5_2,d3_5_3,d3_5_4,d4_5_4]
  ring
#print axioms coefficient_5_4

compact_certificate_declaration theorem coefficient_5_5 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[5]?=some 0 := by
  change some (((((((d0_2_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_5_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_5_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_5_3 y z w b u))+(((d2_0_3 y z w b u)*(d3_5_2 y z w b u))+(((d2_0_4 y z w b u)*(d3_5_1 y z w b u))+(((d2_0_5 y z w b u)*(d3_5_0 y z w b u))+0))))))+((((d2_1_0 y z w b u)*(d3_4_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_4_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_4_3 y z w b u))+(((d2_1_3 y z w b u)*(d3_4_2 y z w b u))+(((d2_1_4 y z w b u)*(d3_4_1 y z w b u))+(((d2_1_5 y z w b u)*(d3_4_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_3_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_3 y z w b u))+(((d2_2_3 y z w b u)*(d3_3_2 y z w b u))+(((d2_2_4 y z w b u)*(d3_3_1 y z w b u))+(((d2_2_5 y z w b u)*(d3_3_0 y z w b u))+0))))))+((((d2_3_0 y z w b u)*(d3_2_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_2_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_2_3 y z w b u))+(((d2_3_3 y z w b u)*(d3_2_2 y z w b u))+(((d2_3_4 y z w b u)*(d3_2_1 y z w b u))+(((d2_3_5 y z w b u)*(d3_2_0 y z w b u))+0))))))+((((d2_4_0 y z w b u)*(d3_1_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_1_4 y z w b u))+(((d2_4_2 y z w b u)*(d3_1_3 y z w b u))+(((d2_4_3 y z w b u)*(d3_1_2 y z w b u))+(((d2_4_4 y z w b u)*(d3_1_1 y z w b u))+(((d2_4_5 y z w b u)*(d3_1_0 y z w b u))+0))))))+(((d2_5_0 y z w b u)*(d3_0_5 y z w b u))+(((d2_5_1 y z w b u)*(d3_0_4 y z w b u))+(((d2_5_2 y z w b u)*(d3_0_3 y z w b u))+(((d2_5_3 y z w b u)*(d3_0_2 y z w b u))+(((d2_5_4 y z w b u)*(d3_0_1 y z w b u))+(((d2_5_5 y z w b u)*(d3_0_0 y z w b u))+0))))))))))))+((-1)*(d4_5_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_5,d0_3_5,d0_4_4,d0_4_5,d0_5_4,d0_5_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d3_4_0,d3_4_1,d3_4_2,d3_4_3,d3_4_4,d3_4_5,d3_5_0,d3_5_1,d3_5_2,d3_5_3,d3_5_4,d3_5_5,d4_5_5]
  ring
#print axioms coefficient_5_5

compact_certificate_declaration theorem coefficient_5_6 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[6]?=some 0 := by
  change some (((((((d0_2_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_5_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_5_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_5_4 y z w b u))+(((d2_0_3 y z w b u)*(d3_5_3 y z w b u))+(((d2_0_4 y z w b u)*(d3_5_2 y z w b u))+((d2_0_5 y z w b u)*(d3_5_1 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_4_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_4_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_4_4 y z w b u))+(((d2_1_3 y z w b u)*(d3_4_3 y z w b u))+(((d2_1_4 y z w b u)*(d3_4_2 y z w b u))+((d2_1_5 y z w b u)*(d3_4_1 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_3_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_4 y z w b u))+(((d2_2_3 y z w b u)*(d3_3_3 y z w b u))+(((d2_2_4 y z w b u)*(d3_3_2 y z w b u))+((d2_2_5 y z w b u)*(d3_3_1 y z w b u)))))))+((((d2_3_0 y z w b u)*(d3_2_6 y z w b u))+(((d2_3_1 y z w b u)*(d3_2_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_2_4 y z w b u))+(((d2_3_3 y z w b u)*(d3_2_3 y z w b u))+(((d2_3_4 y z w b u)*(d3_2_2 y z w b u))+((d2_3_5 y z w b u)*(d3_2_1 y z w b u)))))))+((((d2_4_0 y z w b u)*(d3_1_6 y z w b u))+(((d2_4_1 y z w b u)*(d3_1_5 y z w b u))+(((d2_4_2 y z w b u)*(d3_1_4 y z w b u))+(((d2_4_3 y z w b u)*(d3_1_3 y z w b u))+(((d2_4_4 y z w b u)*(d3_1_2 y z w b u))+((d2_4_5 y z w b u)*(d3_1_1 y z w b u)))))))+(((d2_5_0 y z w b u)*(d3_0_6 y z w b u))+(((d2_5_1 y z w b u)*(d3_0_5 y z w b u))+(((d2_5_2 y z w b u)*(d3_0_4 y z w b u))+(((d2_5_3 y z w b u)*(d3_0_3 y z w b u))+(((d2_5_4 y z w b u)*(d3_0_2 y z w b u))+((d2_5_5 y z w b u)*(d3_0_1 y z w b u)))))))))))))+((-1)*(d4_5_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_6,d0_3_6,d0_4_5,d0_4_6,d0_5_5,d0_5_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d3_4_1,d3_4_2,d3_4_3,d3_4_4,d3_4_5,d3_4_6,d3_5_1,d3_5_2,d3_5_3,d3_5_4,d3_5_5,d3_5_6,d4_5_6]
  ring
#print axioms coefficient_5_6
compact_certificate_declaration theorem coefficient_5_7 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[7]?=some 0 := by
  change some (((((((d0_2_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_5_7 y z w b u))+(((d2_0_1 y z w b u)*(d3_5_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_5_5 y z w b u))+(((d2_0_3 y z w b u)*(d3_5_4 y z w b u))+(((d2_0_4 y z w b u)*(d3_5_3 y z w b u))+((d2_0_5 y z w b u)*(d3_5_2 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_4_7 y z w b u))+(((d2_1_1 y z w b u)*(d3_4_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_4_5 y z w b u))+(((d2_1_3 y z w b u)*(d3_4_4 y z w b u))+(((d2_1_4 y z w b u)*(d3_4_3 y z w b u))+((d2_1_5 y z w b u)*(d3_4_2 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_3_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_5 y z w b u))+(((d2_2_3 y z w b u)*(d3_3_4 y z w b u))+(((d2_2_4 y z w b u)*(d3_3_3 y z w b u))+((d2_2_5 y z w b u)*(d3_3_2 y z w b u)))))))+((((d2_3_0 y z w b u)*(d3_2_7 y z w b u))+(((d2_3_1 y z w b u)*(d3_2_6 y z w b u))+(((d2_3_2 y z w b u)*(d3_2_5 y z w b u))+(((d2_3_3 y z w b u)*(d3_2_4 y z w b u))+(((d2_3_4 y z w b u)*(d3_2_3 y z w b u))+((d2_3_5 y z w b u)*(d3_2_2 y z w b u)))))))+((((d2_4_0 y z w b u)*(d3_1_7 y z w b u))+(((d2_4_1 y z w b u)*(d3_1_6 y z w b u))+(((d2_4_2 y z w b u)*(d3_1_5 y z w b u))+(((d2_4_3 y z w b u)*(d3_1_4 y z w b u))+(((d2_4_4 y z w b u)*(d3_1_3 y z w b u))+((d2_4_5 y z w b u)*(d3_1_2 y z w b u)))))))+(((d2_5_0 y z w b u)*(d3_0_7 y z w b u))+(((d2_5_1 y z w b u)*(d3_0_6 y z w b u))+(((d2_5_2 y z w b u)*(d3_0_5 y z w b u))+(((d2_5_3 y z w b u)*(d3_0_4 y z w b u))+(((d2_5_4 y z w b u)*(d3_0_3 y z w b u))+((d2_5_5 y z w b u)*(d3_0_2 y z w b u)))))))))))))+((-1)*(d4_5_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_7,d0_3_7,d0_4_6,d0_4_7,d0_5_6,d0_5_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d3_4_2,d3_4_3,d3_4_4,d3_4_5,d3_4_6,d3_4_7,d3_5_2,d3_5_3,d3_5_4,d3_5_5,d3_5_6,d3_5_7,d4_5_7]
  ring
#print axioms coefficient_5_7

compact_certificate_declaration theorem coefficient_5_8 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[8]?=some 0 := by
  change some (((((((d0_2_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_5_8 y z w b u))+(((d2_0_1 y z w b u)*(d3_5_7 y z w b u))+(((d2_0_2 y z w b u)*(d3_5_6 y z w b u))+(((d2_0_3 y z w b u)*(d3_5_5 y z w b u))+(((d2_0_4 y z w b u)*(d3_5_4 y z w b u))+((d2_0_5 y z w b u)*(d3_5_3 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_4_8 y z w b u))+(((d2_1_1 y z w b u)*(d3_4_7 y z w b u))+(((d2_1_2 y z w b u)*(d3_4_6 y z w b u))+(((d2_1_3 y z w b u)*(d3_4_5 y z w b u))+(((d2_1_4 y z w b u)*(d3_4_4 y z w b u))+((d2_1_5 y z w b u)*(d3_4_3 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_3_8 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_7 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_6 y z w b u))+(((d2_2_3 y z w b u)*(d3_3_5 y z w b u))+(((d2_2_4 y z w b u)*(d3_3_4 y z w b u))+((d2_2_5 y z w b u)*(d3_3_3 y z w b u)))))))+((((d2_3_0 y z w b u)*(d3_2_8 y z w b u))+(((d2_3_1 y z w b u)*(d3_2_7 y z w b u))+(((d2_3_2 y z w b u)*(d3_2_6 y z w b u))+(((d2_3_3 y z w b u)*(d3_2_5 y z w b u))+(((d2_3_4 y z w b u)*(d3_2_4 y z w b u))+((d2_3_5 y z w b u)*(d3_2_3 y z w b u)))))))+((((d2_4_0 y z w b u)*(d3_1_8 y z w b u))+(((d2_4_1 y z w b u)*(d3_1_7 y z w b u))+(((d2_4_2 y z w b u)*(d3_1_6 y z w b u))+(((d2_4_3 y z w b u)*(d3_1_5 y z w b u))+(((d2_4_4 y z w b u)*(d3_1_4 y z w b u))+((d2_4_5 y z w b u)*(d3_1_3 y z w b u)))))))+(((d2_5_0 y z w b u)*(d3_0_8 y z w b u))+(((d2_5_1 y z w b u)*(d3_0_7 y z w b u))+(((d2_5_2 y z w b u)*(d3_0_6 y z w b u))+(((d2_5_3 y z w b u)*(d3_0_5 y z w b u))+(((d2_5_4 y z w b u)*(d3_0_4 y z w b u))+((d2_5_5 y z w b u)*(d3_0_3 y z w b u)))))))))))))+((-1)*(d4_5_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_8,d0_3_8,d0_4_7,d0_4_8,d0_5_7,d0_5_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d3_3_8,d3_4_3,d3_4_4,d3_4_5,d3_4_6,d3_4_7,d3_4_8,d3_5_3,d3_5_4,d3_5_5,d3_5_6,d3_5_7,d3_5_8,d4_5_8]
  ring
#print axioms coefficient_5_8
compact_certificate_declaration theorem coefficient_5_9 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[9]?=some 0 := by
  change some (((((((d0_2_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_9 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_5_9 y z w b u))+(((d2_0_1 y z w b u)*(d3_5_8 y z w b u))+(((d2_0_2 y z w b u)*(d3_5_7 y z w b u))+(((d2_0_3 y z w b u)*(d3_5_6 y z w b u))+(((d2_0_4 y z w b u)*(d3_5_5 y z w b u))+((d2_0_5 y z w b u)*(d3_5_4 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_4_9 y z w b u))+(((d2_1_1 y z w b u)*(d3_4_8 y z w b u))+(((d2_1_2 y z w b u)*(d3_4_7 y z w b u))+(((d2_1_3 y z w b u)*(d3_4_6 y z w b u))+(((d2_1_4 y z w b u)*(d3_4_5 y z w b u))+((d2_1_5 y z w b u)*(d3_4_4 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_3_9 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_8 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_7 y z w b u))+(((d2_2_3 y z w b u)*(d3_3_6 y z w b u))+(((d2_2_4 y z w b u)*(d3_3_5 y z w b u))+((d2_2_5 y z w b u)*(d3_3_4 y z w b u)))))))+((((d2_3_0 y z w b u)*(d3_2_9 y z w b u))+(((d2_3_1 y z w b u)*(d3_2_8 y z w b u))+(((d2_3_2 y z w b u)*(d3_2_7 y z w b u))+(((d2_3_3 y z w b u)*(d3_2_6 y z w b u))+(((d2_3_4 y z w b u)*(d3_2_5 y z w b u))+((d2_3_5 y z w b u)*(d3_2_4 y z w b u)))))))+((((d2_4_0 y z w b u)*(d3_1_9 y z w b u))+(((d2_4_1 y z w b u)*(d3_1_8 y z w b u))+(((d2_4_2 y z w b u)*(d3_1_7 y z w b u))+(((d2_4_3 y z w b u)*(d3_1_6 y z w b u))+(((d2_4_4 y z w b u)*(d3_1_5 y z w b u))+((d2_4_5 y z w b u)*(d3_1_4 y z w b u)))))))+(((d2_5_1 y z w b u)*(d3_0_8 y z w b u))+(((d2_5_2 y z w b u)*(d3_0_7 y z w b u))+(((d2_5_3 y z w b u)*(d3_0_6 y z w b u))+(((d2_5_4 y z w b u)*(d3_0_5 y z w b u))+((d2_5_5 y z w b u)*(d3_0_4 y z w b u))))))))))))+((-1)*(d4_5_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_9,d0_3_9,d0_4_8,d0_4_9,d0_5_8,d0_5_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_1_9,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_2_9,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d3_3_8,d3_3_9,d3_4_4,d3_4_5,d3_4_6,d3_4_7,d3_4_8,d3_4_9,d3_5_4,d3_5_5,d3_5_6,d3_5_7,d3_5_8,d3_5_9,d4_5_9]
  ring
#print axioms coefficient_5_9
compact_certificate_declaration theorem coefficient_5_10 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[10]?=some 0 := by
  change some (((((((d0_2_10 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_10 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_9 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_10 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_9 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_10 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_5_9 y z w b u))+(((d2_0_2 y z w b u)*(d3_5_8 y z w b u))+(((d2_0_3 y z w b u)*(d3_5_7 y z w b u))+(((d2_0_4 y z w b u)*(d3_5_6 y z w b u))+((d2_0_5 y z w b u)*(d3_5_5 y z w b u))))))+((((d2_1_1 y z w b u)*(d3_4_9 y z w b u))+(((d2_1_2 y z w b u)*(d3_4_8 y z w b u))+(((d2_1_3 y z w b u)*(d3_4_7 y z w b u))+(((d2_1_4 y z w b u)*(d3_4_6 y z w b u))+((d2_1_5 y z w b u)*(d3_4_5 y z w b u))))))+((((d2_2_1 y z w b u)*(d3_3_9 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_8 y z w b u))+(((d2_2_3 y z w b u)*(d3_3_7 y z w b u))+(((d2_2_4 y z w b u)*(d3_3_6 y z w b u))+((d2_2_5 y z w b u)*(d3_3_5 y z w b u))))))+((((d2_3_1 y z w b u)*(d3_2_9 y z w b u))+(((d2_3_2 y z w b u)*(d3_2_8 y z w b u))+(((d2_3_3 y z w b u)*(d3_2_7 y z w b u))+(((d2_3_4 y z w b u)*(d3_2_6 y z w b u))+((d2_3_5 y z w b u)*(d3_2_5 y z w b u))))))+((((d2_4_1 y z w b u)*(d3_1_9 y z w b u))+(((d2_4_2 y z w b u)*(d3_1_8 y z w b u))+(((d2_4_3 y z w b u)*(d3_1_7 y z w b u))+(((d2_4_4 y z w b u)*(d3_1_6 y z w b u))+((d2_4_5 y z w b u)*(d3_1_5 y z w b u))))))+(((d2_5_2 y z w b u)*(d3_0_8 y z w b u))+(((d2_5_3 y z w b u)*(d3_0_7 y z w b u))+(((d2_5_4 y z w b u)*(d3_0_6 y z w b u))+((d2_5_5 y z w b u)*(d3_0_5 y z w b u)))))))))))+((-1)*(d4_5_10 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_10,d0_3_10,d0_4_10,d0_4_9,d0_5_10,d0_5_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_1_9,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_2_9,d3_3_5,d3_3_6,d3_3_7,d3_3_8,d3_3_9,d3_4_5,d3_4_6,d3_4_7,d3_4_8,d3_4_9,d3_5_5,d3_5_6,d3_5_7,d3_5_8,d3_5_9,d4_5_10]
  ring
#print axioms coefficient_5_10

compact_certificate_declaration theorem coefficient_5_11 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[11]?=some 0 := by
  change some ((((((d0_2_11 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_11 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_10 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_11 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_10 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_11 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_5_9 y z w b u))+(((d2_0_3 y z w b u)*(d3_5_8 y z w b u))+(((d2_0_4 y z w b u)*(d3_5_7 y z w b u))+((d2_0_5 y z w b u)*(d3_5_6 y z w b u)))))+((((d2_1_2 y z w b u)*(d3_4_9 y z w b u))+(((d2_1_3 y z w b u)*(d3_4_8 y z w b u))+(((d2_1_4 y z w b u)*(d3_4_7 y z w b u))+((d2_1_5 y z w b u)*(d3_4_6 y z w b u)))))+((((d2_2_2 y z w b u)*(d3_3_9 y z w b u))+(((d2_2_3 y z w b u)*(d3_3_8 y z w b u))+(((d2_2_4 y z w b u)*(d3_3_7 y z w b u))+((d2_2_5 y z w b u)*(d3_3_6 y z w b u)))))+((((d2_3_2 y z w b u)*(d3_2_9 y z w b u))+(((d2_3_3 y z w b u)*(d3_2_8 y z w b u))+(((d2_3_4 y z w b u)*(d3_2_7 y z w b u))+((d2_3_5 y z w b u)*(d3_2_6 y z w b u)))))+((((d2_4_2 y z w b u)*(d3_1_9 y z w b u))+(((d2_4_3 y z w b u)*(d3_1_8 y z w b u))+(((d2_4_4 y z w b u)*(d3_1_7 y z w b u))+((d2_4_5 y z w b u)*(d3_1_6 y z w b u)))))+(((d2_5_3 y z w b u)*(d3_0_8 y z w b u))+(((d2_5_4 y z w b u)*(d3_0_7 y z w b u))+((d2_5_5 y z w b u)*(d3_0_6 y z w b u)))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_11,d0_3_11,d0_4_10,d0_4_11,d0_5_10,d0_5_11,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_3,d2_5_4,d2_5_5,d3_0_6,d3_0_7,d3_0_8,d3_1_6,d3_1_7,d3_1_8,d3_1_9,d3_2_6,d3_2_7,d3_2_8,d3_2_9,d3_3_6,d3_3_7,d3_3_8,d3_3_9,d3_4_6,d3_4_7,d3_4_8,d3_4_9,d3_5_6,d3_5_7,d3_5_8,d3_5_9]
  ring
#print axioms coefficient_5_11
compact_certificate_declaration theorem coefficient_5_12 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[12]?=some 0 := by
  change some ((((((d0_2_12 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_12 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_11 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_12 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_11 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_12 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_3 y z w b u)*(d3_5_9 y z w b u))+(((d2_0_4 y z w b u)*(d3_5_8 y z w b u))+((d2_0_5 y z w b u)*(d3_5_7 y z w b u))))+((((d2_1_3 y z w b u)*(d3_4_9 y z w b u))+(((d2_1_4 y z w b u)*(d3_4_8 y z w b u))+((d2_1_5 y z w b u)*(d3_4_7 y z w b u))))+((((d2_2_3 y z w b u)*(d3_3_9 y z w b u))+(((d2_2_4 y z w b u)*(d3_3_8 y z w b u))+((d2_2_5 y z w b u)*(d3_3_7 y z w b u))))+((((d2_3_3 y z w b u)*(d3_2_9 y z w b u))+(((d2_3_4 y z w b u)*(d3_2_8 y z w b u))+((d2_3_5 y z w b u)*(d3_2_7 y z w b u))))+((((d2_4_3 y z w b u)*(d3_1_9 y z w b u))+(((d2_4_4 y z w b u)*(d3_1_8 y z w b u))+((d2_4_5 y z w b u)*(d3_1_7 y z w b u))))+(((d2_5_4 y z w b u)*(d3_0_8 y z w b u))+((d2_5_5 y z w b u)*(d3_0_7 y z w b u))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_12,d0_3_12,d0_4_11,d0_4_12,d0_5_11,d0_5_12,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_0_4,d2_0_5,d2_1_3,d2_1_4,d2_1_5,d2_2_3,d2_2_4,d2_2_5,d2_3_3,d2_3_4,d2_3_5,d2_4_3,d2_4_4,d2_4_5,d2_5_4,d2_5_5,d3_0_7,d3_0_8,d3_1_7,d3_1_8,d3_1_9,d3_2_7,d3_2_8,d3_2_9,d3_3_7,d3_3_8,d3_3_9,d3_4_7,d3_4_8,d3_4_9,d3_5_7,d3_5_8,d3_5_9]
  ring
#print axioms coefficient_5_12
compact_certificate_declaration theorem coefficient_5_13 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[13]?=some 0 := by
  change some ((((((d0_2_13 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_13 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_12 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_13 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_12 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_13 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_4 y z w b u)*(d3_5_9 y z w b u))+((d2_0_5 y z w b u)*(d3_5_8 y z w b u)))+((((d2_1_4 y z w b u)*(d3_4_9 y z w b u))+((d2_1_5 y z w b u)*(d3_4_8 y z w b u)))+((((d2_2_4 y z w b u)*(d3_3_9 y z w b u))+((d2_2_5 y z w b u)*(d3_3_8 y z w b u)))+((((d2_3_4 y z w b u)*(d3_2_9 y z w b u))+((d2_3_5 y z w b u)*(d3_2_8 y z w b u)))+((((d2_4_4 y z w b u)*(d3_1_9 y z w b u))+((d2_4_5 y z w b u)*(d3_1_8 y z w b u)))+((d2_5_5 y z w b u)*(d3_0_8 y z w b u)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_13,d0_3_13,d0_4_12,d0_4_13,d0_5_12,d0_5_13,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_4,d2_0_5,d2_1_4,d2_1_5,d2_2_4,d2_2_5,d2_3_4,d2_3_5,d2_4_4,d2_4_5,d2_5_5,d3_0_8,d3_1_8,d3_1_9,d3_2_8,d3_2_9,d3_3_8,d3_3_9,d3_4_8,d3_4_9,d3_5_8,d3_5_9]
  ring
#print axioms coefficient_5_13

compact_certificate_declaration theorem coefficient_5_14 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[14]?=some 0 := by
  change some (((((d0_4_13 y z w b u)*(d1_1_1 y z w b u))+((d0_5_13 y z w b u)*(d1_0_1 y z w b u)))+(((d2_0_5 y z w b u)*(d3_5_9 y z w b u))+(((d2_1_5 y z w b u)*(d3_4_9 y z w b u))+(((d2_2_5 y z w b u)*(d3_3_9 y z w b u))+(((d2_3_5 y z w b u)*(d3_2_9 y z w b u))+((d2_4_5 y z w b u)*(d3_1_9 y z w b u))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_13,d0_5_13,d1_0_1,d1_1_1,d2_0_5,d2_1_5,d2_2_5,d2_3_5,d2_4_5,d3_1_9,d3_2_9,d3_3_9,d3_4_9,d3_5_9]
  ring
#print axioms coefficient_5_14

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
compact_certificate_declaration theorem inner_length_6 (y z w b u : ℂ) : (innerCertificate6 y z w b u).length=15 := by
  norm_num [innerCertificate6,add,multiply,scale,inner0_3,inner0_4,inner0_5,inner0_6,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner4_6]
compact_certificate_declaration theorem inner_eval_6 (y z w a b u : ℂ) :
    evaluate a (innerCertificate6 y z w b u)=(((((c0_3 y z w a b u)*(c1_3 y z w a b u))+(((c0_4 y z w a b u)*(c1_2 y z w a b u))+(((c0_5 y z w a b u)*(c1_1 y z w a b u))+(((c0_6 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_6 y z w a b u))+(((c2_1 y z w a b u)*(c3_5 y z w a b u))+(((c2_2 y z w a b u)*(c3_4 y z w a b u))+(((c2_3 y z w a b u)*(c3_3 y z w a b u))+(((c2_4 y z w a b u)*(c3_2 y z w a b u))+(((c2_5 y z w a b u)*(c3_1 y z w a b u))+(((c2_6 y z w a b u)*(c3_0 y z w a b u))+0))))))))+((-1)*(c4_6 y z w a b u))) := by
  simp only [innerCertificate6,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_3,c0_4,c0_5,c0_6,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c3_0,c3_1,c3_2,c3_3,c3_4,c3_5,c3_6,c4_6]
#print axioms inner_eval_6

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

compact_certificate_declaration theorem coefficient_6_0 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[0]?=some 0 := by
  change some (((((((d0_3_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_6_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_6_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_5_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_4_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_3_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_2_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_1_0 y z w b u))+0)+(((d2_6_0 y z w b u)*(d3_0_0 y z w b u))+0))))))))+(((-1)*(d4_6_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_0,d0_4_0,d0_5_0,d0_6_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d4_6_0]
  ring
#print axioms coefficient_6_0
compact_certificate_declaration theorem coefficient_6_1 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[1]?=some 0 := by
  change some (((((((d0_3_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_6_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_6_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_5_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_5_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_4_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_3_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_2_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_2_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_1_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_1_0 y z w b u))+0))+(((d2_6_0 y z w b u)*(d3_0_1 y z w b u))+(((d2_6_1 y z w b u)*(d3_0_0 y z w b u))+0)))))))))+((-1)*(d4_6_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_1,d0_4_1,d0_5_0,d0_5_1,d0_6_0,d0_6_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d2_6_1,d3_0_0,d3_0_1,d3_1_0,d3_1_1,d3_2_0,d3_2_1,d3_3_0,d3_3_1,d3_4_0,d3_4_1,d3_5_0,d3_5_1,d3_6_0,d3_6_1,d4_6_1]
  ring
#print axioms coefficient_6_1
compact_certificate_declaration theorem coefficient_6_2 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[2]?=some 0 := by
  change some (((((((d0_3_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_6_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_6_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_6_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_5_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_5_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_5_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_4_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_3_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_3_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_2_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_2_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_2_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_1_2 y z w b u))+(((d2_5_1 y z w b u)*(d3_1_1 y z w b u))+(((d2_5_2 y z w b u)*(d3_1_0 y z w b u))+0)))+(((d2_6_0 y z w b u)*(d3_0_2 y z w b u))+(((d2_6_1 y z w b u)*(d3_0_1 y z w b u))+(((d2_6_2 y z w b u)*(d3_0_0 y z w b u))+0))))))))))+((-1)*(d4_6_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_2,d0_4_2,d0_5_1,d0_5_2,d0_6_1,d0_6_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_5_2,d2_6_0,d2_6_1,d2_6_2,d3_0_0,d3_0_1,d3_0_2,d3_1_0,d3_1_1,d3_1_2,d3_2_0,d3_2_1,d3_2_2,d3_3_0,d3_3_1,d3_3_2,d3_4_0,d3_4_1,d3_4_2,d3_5_0,d3_5_1,d3_5_2,d3_6_0,d3_6_1,d3_6_2,d4_6_2]
  ring
#print axioms coefficient_6_2

compact_certificate_declaration theorem coefficient_6_3 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[3]?=some 0 := by
  change some (((((((d0_3_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_6_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_6_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_6_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_6_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_5_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_5_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_5_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_5_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_4_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_4_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_3_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_3_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_3_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_2_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_2_2 y z w b u))+(((d2_4_2 y z w b u)*(d3_2_1 y z w b u))+(((d2_4_3 y z w b u)*(d3_2_0 y z w b u))+0))))+((((d2_5_0 y z w b u)*(d3_1_3 y z w b u))+(((d2_5_1 y z w b u)*(d3_1_2 y z w b u))+(((d2_5_2 y z w b u)*(d3_1_1 y z w b u))+(((d2_5_3 y z w b u)*(d3_1_0 y z w b u))+0))))+(((d2_6_0 y z w b u)*(d3_0_3 y z w b u))+(((d2_6_1 y z w b u)*(d3_0_2 y z w b u))+(((d2_6_2 y z w b u)*(d3_0_1 y z w b u))+(((d2_6_3 y z w b u)*(d3_0_0 y z w b u))+0)))))))))))+((-1)*(d4_6_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_3,d0_4_3,d0_5_2,d0_5_3,d0_6_2,d0_6_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d3_4_0,d3_4_1,d3_4_2,d3_4_3,d3_5_0,d3_5_1,d3_5_2,d3_5_3,d3_6_0,d3_6_1,d3_6_2,d3_6_3,d4_6_3]
  ring
#print axioms coefficient_6_3

compact_certificate_declaration theorem coefficient_6_4 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[4]?=some 0 := by
  change some (((((((d0_3_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_6_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_6_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_6_2 y z w b u))+(((d2_0_3 y z w b u)*(d3_6_1 y z w b u))+(((d2_0_4 y z w b u)*(d3_6_0 y z w b u))+0)))))+((((d2_1_0 y z w b u)*(d3_5_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_5_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_5_2 y z w b u))+(((d2_1_3 y z w b u)*(d3_5_1 y z w b u))+(((d2_1_4 y z w b u)*(d3_5_0 y z w b u))+0)))))+((((d2_2_0 y z w b u)*(d3_4_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_2 y z w b u))+(((d2_2_3 y z w b u)*(d3_4_1 y z w b u))+(((d2_2_4 y z w b u)*(d3_4_0 y z w b u))+0)))))+((((d2_3_0 y z w b u)*(d3_3_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_3_2 y z w b u))+(((d2_3_3 y z w b u)*(d3_3_1 y z w b u))+(((d2_3_4 y z w b u)*(d3_3_0 y z w b u))+0)))))+((((d2_4_0 y z w b u)*(d3_2_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_2_3 y z w b u))+(((d2_4_2 y z w b u)*(d3_2_2 y z w b u))+(((d2_4_3 y z w b u)*(d3_2_1 y z w b u))+(((d2_4_4 y z w b u)*(d3_2_0 y z w b u))+0)))))+((((d2_5_0 y z w b u)*(d3_1_4 y z w b u))+(((d2_5_1 y z w b u)*(d3_1_3 y z w b u))+(((d2_5_2 y z w b u)*(d3_1_2 y z w b u))+(((d2_5_3 y z w b u)*(d3_1_1 y z w b u))+(((d2_5_4 y z w b u)*(d3_1_0 y z w b u))+0)))))+(((d2_6_0 y z w b u)*(d3_0_4 y z w b u))+(((d2_6_1 y z w b u)*(d3_0_3 y z w b u))+(((d2_6_2 y z w b u)*(d3_0_2 y z w b u))+(((d2_6_3 y z w b u)*(d3_0_1 y z w b u))+(((d2_6_4 y z w b u)*(d3_0_0 y z w b u))+0))))))))))))+((-1)*(d4_6_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_4,d0_4_4,d0_5_3,d0_5_4,d0_6_3,d0_6_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d3_4_0,d3_4_1,d3_4_2,d3_4_3,d3_4_4,d3_5_0,d3_5_1,d3_5_2,d3_5_3,d3_5_4,d3_6_0,d3_6_1,d3_6_2,d3_6_3,d3_6_4,d4_6_4]
  ring
#print axioms coefficient_6_4

compact_certificate_declaration theorem coefficient_6_5 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[5]?=some 0 := by
  change some (((((((d0_3_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_6_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_6_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_6_3 y z w b u))+(((d2_0_3 y z w b u)*(d3_6_2 y z w b u))+(((d2_0_4 y z w b u)*(d3_6_1 y z w b u))+(((d2_0_5 y z w b u)*(d3_6_0 y z w b u))+0))))))+((((d2_1_0 y z w b u)*(d3_5_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_5_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_5_3 y z w b u))+(((d2_1_3 y z w b u)*(d3_5_2 y z w b u))+(((d2_1_4 y z w b u)*(d3_5_1 y z w b u))+(((d2_1_5 y z w b u)*(d3_5_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_4_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_3 y z w b u))+(((d2_2_3 y z w b u)*(d3_4_2 y z w b u))+(((d2_2_4 y z w b u)*(d3_4_1 y z w b u))+(((d2_2_5 y z w b u)*(d3_4_0 y z w b u))+0))))))+((((d2_3_0 y z w b u)*(d3_3_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_3_3 y z w b u))+(((d2_3_3 y z w b u)*(d3_3_2 y z w b u))+(((d2_3_4 y z w b u)*(d3_3_1 y z w b u))+(((d2_3_5 y z w b u)*(d3_3_0 y z w b u))+0))))))+((((d2_4_0 y z w b u)*(d3_2_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_2_4 y z w b u))+(((d2_4_2 y z w b u)*(d3_2_3 y z w b u))+(((d2_4_3 y z w b u)*(d3_2_2 y z w b u))+(((d2_4_4 y z w b u)*(d3_2_1 y z w b u))+(((d2_4_5 y z w b u)*(d3_2_0 y z w b u))+0))))))+((((d2_5_0 y z w b u)*(d3_1_5 y z w b u))+(((d2_5_1 y z w b u)*(d3_1_4 y z w b u))+(((d2_5_2 y z w b u)*(d3_1_3 y z w b u))+(((d2_5_3 y z w b u)*(d3_1_2 y z w b u))+(((d2_5_4 y z w b u)*(d3_1_1 y z w b u))+(((d2_5_5 y z w b u)*(d3_1_0 y z w b u))+0))))))+(((d2_6_0 y z w b u)*(d3_0_5 y z w b u))+(((d2_6_1 y z w b u)*(d3_0_4 y z w b u))+(((d2_6_2 y z w b u)*(d3_0_3 y z w b u))+(((d2_6_3 y z w b u)*(d3_0_2 y z w b u))+((d2_6_4 y z w b u)*(d3_0_1 y z w b u)))))))))))))+((-1)*(d4_6_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_5,d0_4_5,d0_5_4,d0_5_5,d0_6_4,d0_6_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d3_4_0,d3_4_1,d3_4_2,d3_4_3,d3_4_4,d3_4_5,d3_5_0,d3_5_1,d3_5_2,d3_5_3,d3_5_4,d3_5_5,d3_6_0,d3_6_1,d3_6_2,d3_6_3,d3_6_4,d3_6_5,d4_6_5]
  ring
#print axioms coefficient_6_5

compact_certificate_declaration theorem coefficient_6_6 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[6]?=some 0 := by
  change some (((((((d0_3_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_6_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_6_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_6_4 y z w b u))+(((d2_0_3 y z w b u)*(d3_6_3 y z w b u))+(((d2_0_4 y z w b u)*(d3_6_2 y z w b u))+((d2_0_5 y z w b u)*(d3_6_1 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_5_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_5_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_5_4 y z w b u))+(((d2_1_3 y z w b u)*(d3_5_3 y z w b u))+(((d2_1_4 y z w b u)*(d3_5_2 y z w b u))+((d2_1_5 y z w b u)*(d3_5_1 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_4_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_4 y z w b u))+(((d2_2_3 y z w b u)*(d3_4_3 y z w b u))+(((d2_2_4 y z w b u)*(d3_4_2 y z w b u))+((d2_2_5 y z w b u)*(d3_4_1 y z w b u)))))))+((((d2_3_0 y z w b u)*(d3_3_6 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_3_4 y z w b u))+(((d2_3_3 y z w b u)*(d3_3_3 y z w b u))+(((d2_3_4 y z w b u)*(d3_3_2 y z w b u))+((d2_3_5 y z w b u)*(d3_3_1 y z w b u)))))))+((((d2_4_0 y z w b u)*(d3_2_6 y z w b u))+(((d2_4_1 y z w b u)*(d3_2_5 y z w b u))+(((d2_4_2 y z w b u)*(d3_2_4 y z w b u))+(((d2_4_3 y z w b u)*(d3_2_3 y z w b u))+(((d2_4_4 y z w b u)*(d3_2_2 y z w b u))+((d2_4_5 y z w b u)*(d3_2_1 y z w b u)))))))+((((d2_5_0 y z w b u)*(d3_1_6 y z w b u))+(((d2_5_1 y z w b u)*(d3_1_5 y z w b u))+(((d2_5_2 y z w b u)*(d3_1_4 y z w b u))+(((d2_5_3 y z w b u)*(d3_1_3 y z w b u))+(((d2_5_4 y z w b u)*(d3_1_2 y z w b u))+((d2_5_5 y z w b u)*(d3_1_1 y z w b u)))))))+(((d2_6_0 y z w b u)*(d3_0_6 y z w b u))+(((d2_6_1 y z w b u)*(d3_0_5 y z w b u))+(((d2_6_2 y z w b u)*(d3_0_4 y z w b u))+(((d2_6_3 y z w b u)*(d3_0_3 y z w b u))+((d2_6_4 y z w b u)*(d3_0_2 y z w b u)))))))))))))+((-1)*(d4_6_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_6,d0_4_6,d0_5_5,d0_5_6,d0_6_5,d0_6_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d3_4_1,d3_4_2,d3_4_3,d3_4_4,d3_4_5,d3_4_6,d3_5_1,d3_5_2,d3_5_3,d3_5_4,d3_5_5,d3_5_6,d3_6_1,d3_6_2,d3_6_3,d3_6_4,d3_6_5,d3_6_6,d4_6_6]
  ring
#print axioms coefficient_6_6

compact_certificate_declaration theorem coefficient_6_7 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[7]?=some 0 := by
  change some (((((((d0_3_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_6_7 y z w b u))+(((d2_0_1 y z w b u)*(d3_6_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_6_5 y z w b u))+(((d2_0_3 y z w b u)*(d3_6_4 y z w b u))+(((d2_0_4 y z w b u)*(d3_6_3 y z w b u))+((d2_0_5 y z w b u)*(d3_6_2 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_5_7 y z w b u))+(((d2_1_1 y z w b u)*(d3_5_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_5_5 y z w b u))+(((d2_1_3 y z w b u)*(d3_5_4 y z w b u))+(((d2_1_4 y z w b u)*(d3_5_3 y z w b u))+((d2_1_5 y z w b u)*(d3_5_2 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_4_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_5 y z w b u))+(((d2_2_3 y z w b u)*(d3_4_4 y z w b u))+(((d2_2_4 y z w b u)*(d3_4_3 y z w b u))+((d2_2_5 y z w b u)*(d3_4_2 y z w b u)))))))+((((d2_3_0 y z w b u)*(d3_3_7 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_6 y z w b u))+(((d2_3_2 y z w b u)*(d3_3_5 y z w b u))+(((d2_3_3 y z w b u)*(d3_3_4 y z w b u))+(((d2_3_4 y z w b u)*(d3_3_3 y z w b u))+((d2_3_5 y z w b u)*(d3_3_2 y z w b u)))))))+((((d2_4_0 y z w b u)*(d3_2_7 y z w b u))+(((d2_4_1 y z w b u)*(d3_2_6 y z w b u))+(((d2_4_2 y z w b u)*(d3_2_5 y z w b u))+(((d2_4_3 y z w b u)*(d3_2_4 y z w b u))+(((d2_4_4 y z w b u)*(d3_2_3 y z w b u))+((d2_4_5 y z w b u)*(d3_2_2 y z w b u)))))))+((((d2_5_0 y z w b u)*(d3_1_7 y z w b u))+(((d2_5_1 y z w b u)*(d3_1_6 y z w b u))+(((d2_5_2 y z w b u)*(d3_1_5 y z w b u))+(((d2_5_3 y z w b u)*(d3_1_4 y z w b u))+(((d2_5_4 y z w b u)*(d3_1_3 y z w b u))+((d2_5_5 y z w b u)*(d3_1_2 y z w b u)))))))+(((d2_6_0 y z w b u)*(d3_0_7 y z w b u))+(((d2_6_1 y z w b u)*(d3_0_6 y z w b u))+(((d2_6_2 y z w b u)*(d3_0_5 y z w b u))+(((d2_6_3 y z w b u)*(d3_0_4 y z w b u))+((d2_6_4 y z w b u)*(d3_0_3 y z w b u)))))))))))))+((-1)*(d4_6_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_7,d0_4_7,d0_5_6,d0_5_7,d0_6_6,d0_6_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d3_4_2,d3_4_3,d3_4_4,d3_4_5,d3_4_6,d3_4_7,d3_5_2,d3_5_3,d3_5_4,d3_5_5,d3_5_6,d3_5_7,d3_6_2,d3_6_3,d3_6_4,d3_6_5,d3_6_6,d3_6_7,d4_6_7]
  ring
#print axioms coefficient_6_7
compact_certificate_declaration theorem coefficient_6_8 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[8]?=some 0 := by
  change some (((((((d0_3_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_6_8 y z w b u))+(((d2_0_1 y z w b u)*(d3_6_7 y z w b u))+(((d2_0_2 y z w b u)*(d3_6_6 y z w b u))+(((d2_0_3 y z w b u)*(d3_6_5 y z w b u))+(((d2_0_4 y z w b u)*(d3_6_4 y z w b u))+((d2_0_5 y z w b u)*(d3_6_3 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_5_8 y z w b u))+(((d2_1_1 y z w b u)*(d3_5_7 y z w b u))+(((d2_1_2 y z w b u)*(d3_5_6 y z w b u))+(((d2_1_3 y z w b u)*(d3_5_5 y z w b u))+(((d2_1_4 y z w b u)*(d3_5_4 y z w b u))+((d2_1_5 y z w b u)*(d3_5_3 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_4_8 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_7 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_6 y z w b u))+(((d2_2_3 y z w b u)*(d3_4_5 y z w b u))+(((d2_2_4 y z w b u)*(d3_4_4 y z w b u))+((d2_2_5 y z w b u)*(d3_4_3 y z w b u)))))))+((((d2_3_0 y z w b u)*(d3_3_8 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_7 y z w b u))+(((d2_3_2 y z w b u)*(d3_3_6 y z w b u))+(((d2_3_3 y z w b u)*(d3_3_5 y z w b u))+(((d2_3_4 y z w b u)*(d3_3_4 y z w b u))+((d2_3_5 y z w b u)*(d3_3_3 y z w b u)))))))+((((d2_4_0 y z w b u)*(d3_2_8 y z w b u))+(((d2_4_1 y z w b u)*(d3_2_7 y z w b u))+(((d2_4_2 y z w b u)*(d3_2_6 y z w b u))+(((d2_4_3 y z w b u)*(d3_2_5 y z w b u))+(((d2_4_4 y z w b u)*(d3_2_4 y z w b u))+((d2_4_5 y z w b u)*(d3_2_3 y z w b u)))))))+((((d2_5_0 y z w b u)*(d3_1_8 y z w b u))+(((d2_5_1 y z w b u)*(d3_1_7 y z w b u))+(((d2_5_2 y z w b u)*(d3_1_6 y z w b u))+(((d2_5_3 y z w b u)*(d3_1_5 y z w b u))+(((d2_5_4 y z w b u)*(d3_1_4 y z w b u))+((d2_5_5 y z w b u)*(d3_1_3 y z w b u)))))))+(((d2_6_0 y z w b u)*(d3_0_8 y z w b u))+(((d2_6_1 y z w b u)*(d3_0_7 y z w b u))+(((d2_6_2 y z w b u)*(d3_0_6 y z w b u))+(((d2_6_3 y z w b u)*(d3_0_5 y z w b u))+((d2_6_4 y z w b u)*(d3_0_4 y z w b u)))))))))))))+((-1)*(d4_6_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_8,d0_4_8,d0_5_7,d0_5_8,d0_6_7,d0_6_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d3_3_8,d3_4_3,d3_4_4,d3_4_5,d3_4_6,d3_4_7,d3_4_8,d3_5_3,d3_5_4,d3_5_5,d3_5_6,d3_5_7,d3_5_8,d3_6_3,d3_6_4,d3_6_5,d3_6_6,d3_6_7,d3_6_8,d4_6_8]
  ring
#print axioms coefficient_6_8

compact_certificate_declaration theorem coefficient_6_9 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[9]?=some 0 := by
  change some (((((((d0_3_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_9 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_6_9 y z w b u))+(((d2_0_1 y z w b u)*(d3_6_8 y z w b u))+(((d2_0_2 y z w b u)*(d3_6_7 y z w b u))+(((d2_0_3 y z w b u)*(d3_6_6 y z w b u))+(((d2_0_4 y z w b u)*(d3_6_5 y z w b u))+((d2_0_5 y z w b u)*(d3_6_4 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_5_9 y z w b u))+(((d2_1_1 y z w b u)*(d3_5_8 y z w b u))+(((d2_1_2 y z w b u)*(d3_5_7 y z w b u))+(((d2_1_3 y z w b u)*(d3_5_6 y z w b u))+(((d2_1_4 y z w b u)*(d3_5_5 y z w b u))+((d2_1_5 y z w b u)*(d3_5_4 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_4_9 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_8 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_7 y z w b u))+(((d2_2_3 y z w b u)*(d3_4_6 y z w b u))+(((d2_2_4 y z w b u)*(d3_4_5 y z w b u))+((d2_2_5 y z w b u)*(d3_4_4 y z w b u)))))))+((((d2_3_0 y z w b u)*(d3_3_9 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_8 y z w b u))+(((d2_3_2 y z w b u)*(d3_3_7 y z w b u))+(((d2_3_3 y z w b u)*(d3_3_6 y z w b u))+(((d2_3_4 y z w b u)*(d3_3_5 y z w b u))+((d2_3_5 y z w b u)*(d3_3_4 y z w b u)))))))+((((d2_4_0 y z w b u)*(d3_2_9 y z w b u))+(((d2_4_1 y z w b u)*(d3_2_8 y z w b u))+(((d2_4_2 y z w b u)*(d3_2_7 y z w b u))+(((d2_4_3 y z w b u)*(d3_2_6 y z w b u))+(((d2_4_4 y z w b u)*(d3_2_5 y z w b u))+((d2_4_5 y z w b u)*(d3_2_4 y z w b u)))))))+((((d2_5_0 y z w b u)*(d3_1_9 y z w b u))+(((d2_5_1 y z w b u)*(d3_1_8 y z w b u))+(((d2_5_2 y z w b u)*(d3_1_7 y z w b u))+(((d2_5_3 y z w b u)*(d3_1_6 y z w b u))+(((d2_5_4 y z w b u)*(d3_1_5 y z w b u))+((d2_5_5 y z w b u)*(d3_1_4 y z w b u)))))))+(((d2_6_1 y z w b u)*(d3_0_8 y z w b u))+(((d2_6_2 y z w b u)*(d3_0_7 y z w b u))+(((d2_6_3 y z w b u)*(d3_0_6 y z w b u))+((d2_6_4 y z w b u)*(d3_0_5 y z w b u))))))))))))+((-1)*(d4_6_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_9,d0_4_9,d0_5_8,d0_5_9,d0_6_8,d0_6_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_1_9,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_2_9,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d3_3_8,d3_3_9,d3_4_4,d3_4_5,d3_4_6,d3_4_7,d3_4_8,d3_4_9,d3_5_4,d3_5_5,d3_5_6,d3_5_7,d3_5_8,d3_5_9,d3_6_4,d3_6_5,d3_6_6,d3_6_7,d3_6_8,d3_6_9,d4_6_9]
  ring
#print axioms coefficient_6_9
compact_certificate_declaration theorem coefficient_6_10 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[10]?=some 0 := by
  change some (((((((d0_3_10 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_10 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_9 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_10 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_9 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_10 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_6_9 y z w b u))+(((d2_0_2 y z w b u)*(d3_6_8 y z w b u))+(((d2_0_3 y z w b u)*(d3_6_7 y z w b u))+(((d2_0_4 y z w b u)*(d3_6_6 y z w b u))+((d2_0_5 y z w b u)*(d3_6_5 y z w b u))))))+((((d2_1_1 y z w b u)*(d3_5_9 y z w b u))+(((d2_1_2 y z w b u)*(d3_5_8 y z w b u))+(((d2_1_3 y z w b u)*(d3_5_7 y z w b u))+(((d2_1_4 y z w b u)*(d3_5_6 y z w b u))+((d2_1_5 y z w b u)*(d3_5_5 y z w b u))))))+((((d2_2_1 y z w b u)*(d3_4_9 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_8 y z w b u))+(((d2_2_3 y z w b u)*(d3_4_7 y z w b u))+(((d2_2_4 y z w b u)*(d3_4_6 y z w b u))+((d2_2_5 y z w b u)*(d3_4_5 y z w b u))))))+((((d2_3_1 y z w b u)*(d3_3_9 y z w b u))+(((d2_3_2 y z w b u)*(d3_3_8 y z w b u))+(((d2_3_3 y z w b u)*(d3_3_7 y z w b u))+(((d2_3_4 y z w b u)*(d3_3_6 y z w b u))+((d2_3_5 y z w b u)*(d3_3_5 y z w b u))))))+((((d2_4_1 y z w b u)*(d3_2_9 y z w b u))+(((d2_4_2 y z w b u)*(d3_2_8 y z w b u))+(((d2_4_3 y z w b u)*(d3_2_7 y z w b u))+(((d2_4_4 y z w b u)*(d3_2_6 y z w b u))+((d2_4_5 y z w b u)*(d3_2_5 y z w b u))))))+((((d2_5_1 y z w b u)*(d3_1_9 y z w b u))+(((d2_5_2 y z w b u)*(d3_1_8 y z w b u))+(((d2_5_3 y z w b u)*(d3_1_7 y z w b u))+(((d2_5_4 y z w b u)*(d3_1_6 y z w b u))+((d2_5_5 y z w b u)*(d3_1_5 y z w b u))))))+(((d2_6_2 y z w b u)*(d3_0_8 y z w b u))+(((d2_6_3 y z w b u)*(d3_0_7 y z w b u))+((d2_6_4 y z w b u)*(d3_0_6 y z w b u)))))))))))+((-1)*(d4_6_10 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_10,d0_4_10,d0_5_10,d0_5_9,d0_6_10,d0_6_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_2,d2_6_3,d2_6_4,d3_0_6,d3_0_7,d3_0_8,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_1_9,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_2_9,d3_3_5,d3_3_6,d3_3_7,d3_3_8,d3_3_9,d3_4_5,d3_4_6,d3_4_7,d3_4_8,d3_4_9,d3_5_5,d3_5_6,d3_5_7,d3_5_8,d3_5_9,d3_6_5,d3_6_6,d3_6_7,d3_6_8,d3_6_9,d4_6_10]
  ring
#print axioms coefficient_6_10
compact_certificate_declaration theorem coefficient_6_11 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[11]?=some 0 := by
  change some (((((((d0_3_11 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_11 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_10 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_11 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_10 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_11 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_6_9 y z w b u))+(((d2_0_3 y z w b u)*(d3_6_8 y z w b u))+(((d2_0_4 y z w b u)*(d3_6_7 y z w b u))+((d2_0_5 y z w b u)*(d3_6_6 y z w b u)))))+((((d2_1_2 y z w b u)*(d3_5_9 y z w b u))+(((d2_1_3 y z w b u)*(d3_5_8 y z w b u))+(((d2_1_4 y z w b u)*(d3_5_7 y z w b u))+((d2_1_5 y z w b u)*(d3_5_6 y z w b u)))))+((((d2_2_2 y z w b u)*(d3_4_9 y z w b u))+(((d2_2_3 y z w b u)*(d3_4_8 y z w b u))+(((d2_2_4 y z w b u)*(d3_4_7 y z w b u))+((d2_2_5 y z w b u)*(d3_4_6 y z w b u)))))+((((d2_3_2 y z w b u)*(d3_3_9 y z w b u))+(((d2_3_3 y z w b u)*(d3_3_8 y z w b u))+(((d2_3_4 y z w b u)*(d3_3_7 y z w b u))+((d2_3_5 y z w b u)*(d3_3_6 y z w b u)))))+((((d2_4_2 y z w b u)*(d3_2_9 y z w b u))+(((d2_4_3 y z w b u)*(d3_2_8 y z w b u))+(((d2_4_4 y z w b u)*(d3_2_7 y z w b u))+((d2_4_5 y z w b u)*(d3_2_6 y z w b u)))))+((((d2_5_2 y z w b u)*(d3_1_9 y z w b u))+(((d2_5_3 y z w b u)*(d3_1_8 y z w b u))+(((d2_5_4 y z w b u)*(d3_1_7 y z w b u))+((d2_5_5 y z w b u)*(d3_1_6 y z w b u)))))+(((d2_6_3 y z w b u)*(d3_0_8 y z w b u))+((d2_6_4 y z w b u)*(d3_0_7 y z w b u))))))))))+((-1)*(d4_6_11 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_11,d0_4_11,d0_5_10,d0_5_11,d0_6_10,d0_6_11,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_3,d2_6_4,d3_0_7,d3_0_8,d3_1_6,d3_1_7,d3_1_8,d3_1_9,d3_2_6,d3_2_7,d3_2_8,d3_2_9,d3_3_6,d3_3_7,d3_3_8,d3_3_9,d3_4_6,d3_4_7,d3_4_8,d3_4_9,d3_5_6,d3_5_7,d3_5_8,d3_5_9,d3_6_6,d3_6_7,d3_6_8,d3_6_9,d4_6_11]
  ring
#print axioms coefficient_6_11

compact_certificate_declaration theorem coefficient_6_12 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[12]?=some 0 := by
  change some ((((((d0_3_12 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_12 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_11 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_12 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_11 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_12 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_3 y z w b u)*(d3_6_9 y z w b u))+(((d2_0_4 y z w b u)*(d3_6_8 y z w b u))+((d2_0_5 y z w b u)*(d3_6_7 y z w b u))))+((((d2_1_3 y z w b u)*(d3_5_9 y z w b u))+(((d2_1_4 y z w b u)*(d3_5_8 y z w b u))+((d2_1_5 y z w b u)*(d3_5_7 y z w b u))))+((((d2_2_3 y z w b u)*(d3_4_9 y z w b u))+(((d2_2_4 y z w b u)*(d3_4_8 y z w b u))+((d2_2_5 y z w b u)*(d3_4_7 y z w b u))))+((((d2_3_3 y z w b u)*(d3_3_9 y z w b u))+(((d2_3_4 y z w b u)*(d3_3_8 y z w b u))+((d2_3_5 y z w b u)*(d3_3_7 y z w b u))))+((((d2_4_3 y z w b u)*(d3_2_9 y z w b u))+(((d2_4_4 y z w b u)*(d3_2_8 y z w b u))+((d2_4_5 y z w b u)*(d3_2_7 y z w b u))))+((((d2_5_3 y z w b u)*(d3_1_9 y z w b u))+(((d2_5_4 y z w b u)*(d3_1_8 y z w b u))+((d2_5_5 y z w b u)*(d3_1_7 y z w b u))))+((d2_6_4 y z w b u)*(d3_0_8 y z w b u))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_12,d0_4_12,d0_5_11,d0_5_12,d0_6_11,d0_6_12,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_0_4,d2_0_5,d2_1_3,d2_1_4,d2_1_5,d2_2_3,d2_2_4,d2_2_5,d2_3_3,d2_3_4,d2_3_5,d2_4_3,d2_4_4,d2_4_5,d2_5_3,d2_5_4,d2_5_5,d2_6_4,d3_0_8,d3_1_7,d3_1_8,d3_1_9,d3_2_7,d3_2_8,d3_2_9,d3_3_7,d3_3_8,d3_3_9,d3_4_7,d3_4_8,d3_4_9,d3_5_7,d3_5_8,d3_5_9,d3_6_7,d3_6_8,d3_6_9]
  ring
#print axioms coefficient_6_12
compact_certificate_declaration theorem coefficient_6_13 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[13]?=some 0 := by
  change some ((((((d0_3_13 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_13 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_12 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_13 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_12 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_13 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_4 y z w b u)*(d3_6_9 y z w b u))+((d2_0_5 y z w b u)*(d3_6_8 y z w b u)))+((((d2_1_4 y z w b u)*(d3_5_9 y z w b u))+((d2_1_5 y z w b u)*(d3_5_8 y z w b u)))+((((d2_2_4 y z w b u)*(d3_4_9 y z w b u))+((d2_2_5 y z w b u)*(d3_4_8 y z w b u)))+((((d2_3_4 y z w b u)*(d3_3_9 y z w b u))+((d2_3_5 y z w b u)*(d3_3_8 y z w b u)))+((((d2_4_4 y z w b u)*(d3_2_9 y z w b u))+((d2_4_5 y z w b u)*(d3_2_8 y z w b u)))+(((d2_5_4 y z w b u)*(d3_1_9 y z w b u))+((d2_5_5 y z w b u)*(d3_1_8 y z w b u))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_13,d0_4_13,d0_5_12,d0_5_13,d0_6_12,d0_6_13,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_4,d2_0_5,d2_1_4,d2_1_5,d2_2_4,d2_2_5,d2_3_4,d2_3_5,d2_4_4,d2_4_5,d2_5_4,d2_5_5,d3_1_8,d3_1_9,d3_2_8,d3_2_9,d3_3_8,d3_3_9,d3_4_8,d3_4_9,d3_5_8,d3_5_9,d3_6_8,d3_6_9]
  ring
#print axioms coefficient_6_13
compact_certificate_declaration theorem coefficient_6_14 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[14]?=some 0 := by
  change some (((((d0_5_13 y z w b u)*(d1_1_1 y z w b u))+((d0_6_13 y z w b u)*(d1_0_1 y z w b u)))+(((d2_0_5 y z w b u)*(d3_6_9 y z w b u))+(((d2_1_5 y z w b u)*(d3_5_9 y z w b u))+(((d2_2_5 y z w b u)*(d3_4_9 y z w b u))+(((d2_3_5 y z w b u)*(d3_3_9 y z w b u))+(((d2_4_5 y z w b u)*(d3_2_9 y z w b u))+((d2_5_5 y z w b u)*(d3_1_9 y z w b u)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_5_13,d0_6_13,d1_0_1,d1_1_1,d2_0_5,d2_1_5,d2_2_5,d2_3_5,d2_4_5,d2_5_5,d3_1_9,d3_2_9,d3_3_9,d3_4_9,d3_5_9,d3_6_9]
  ring
#print axioms coefficient_6_14

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
compact_certificate_declaration theorem inner_length_7 (y z w b u : ℂ) : (innerCertificate7 y z w b u).length=15 := by
  norm_num [innerCertificate7,add,multiply,scale,inner0_4,inner0_5,inner0_6,inner0_7,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner4_7]
compact_certificate_declaration theorem inner_eval_7 (y z w a b u : ℂ) :
    evaluate a (innerCertificate7 y z w b u)=(((((c0_4 y z w a b u)*(c1_3 y z w a b u))+(((c0_5 y z w a b u)*(c1_2 y z w a b u))+(((c0_6 y z w a b u)*(c1_1 y z w a b u))+(((c0_7 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_7 y z w a b u))+(((c2_1 y z w a b u)*(c3_6 y z w a b u))+(((c2_2 y z w a b u)*(c3_5 y z w a b u))+(((c2_3 y z w a b u)*(c3_4 y z w a b u))+(((c2_4 y z w a b u)*(c3_3 y z w a b u))+(((c2_5 y z w a b u)*(c3_2 y z w a b u))+(((c2_6 y z w a b u)*(c3_1 y z w a b u))+(((c2_7 y z w a b u)*(c3_0 y z w a b u))+0)))))))))+((-1)*(c4_7 y z w a b u))) := by
  simp only [innerCertificate7,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_4,c0_5,c0_6,c0_7,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c3_0,c3_1,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c4_7]
#print axioms inner_eval_7

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

compact_certificate_declaration theorem coefficient_7_0 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[0]?=some 0 := by
  change some (((((((d0_4_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_7_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_7_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_6_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_5_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_4_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_3_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_2_0 y z w b u))+0)+((((d2_6_0 y z w b u)*(d3_1_0 y z w b u))+0)+(((d2_7_0 y z w b u)*(d3_0_0 y z w b u))+0)))))))))+(((-1)*(d4_7_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_0,d0_5_0,d0_6_0,d0_7_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d2_7_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d4_7_0]
  ring
#print axioms coefficient_7_0
compact_certificate_declaration theorem coefficient_7_1 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[1]?=some 0 := by
  change some (((((((d0_4_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_7_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_7_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_6_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_6_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_5_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_4_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_3_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_3_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_2_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_2_0 y z w b u))+0))+((((d2_6_0 y z w b u)*(d3_1_1 y z w b u))+(((d2_6_1 y z w b u)*(d3_1_0 y z w b u))+0))+(((d2_7_0 y z w b u)*(d3_0_1 y z w b u))+(((d2_7_1 y z w b u)*(d3_0_0 y z w b u))+0))))))))))+((-1)*(d4_7_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_1,d0_5_1,d0_6_0,d0_6_1,d0_7_0,d0_7_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d2_6_1,d2_7_0,d2_7_1,d3_0_0,d3_0_1,d3_1_0,d3_1_1,d3_2_0,d3_2_1,d3_3_0,d3_3_1,d3_4_0,d3_4_1,d3_5_0,d3_5_1,d3_6_0,d3_6_1,d3_7_0,d3_7_1,d4_7_1]
  ring
#print axioms coefficient_7_1

compact_certificate_declaration theorem coefficient_7_2 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[2]?=some 0 := by
  change some (((((((d0_4_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_7_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_7_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_7_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_6_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_6_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_6_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_5_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_4_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_4_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_3_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_3_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_3_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_2_2 y z w b u))+(((d2_5_1 y z w b u)*(d3_2_1 y z w b u))+(((d2_5_2 y z w b u)*(d3_2_0 y z w b u))+0)))+((((d2_6_0 y z w b u)*(d3_1_2 y z w b u))+(((d2_6_1 y z w b u)*(d3_1_1 y z w b u))+(((d2_6_2 y z w b u)*(d3_1_0 y z w b u))+0)))+(((d2_7_0 y z w b u)*(d3_0_2 y z w b u))+(((d2_7_1 y z w b u)*(d3_0_1 y z w b u))+(((d2_7_2 y z w b u)*(d3_0_0 y z w b u))+0)))))))))))+((-1)*(d4_7_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_2,d0_5_2,d0_6_1,d0_6_2,d0_7_1,d0_7_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_5_2,d2_6_0,d2_6_1,d2_6_2,d2_7_0,d2_7_1,d2_7_2,d3_0_0,d3_0_1,d3_0_2,d3_1_0,d3_1_1,d3_1_2,d3_2_0,d3_2_1,d3_2_2,d3_3_0,d3_3_1,d3_3_2,d3_4_0,d3_4_1,d3_4_2,d3_5_0,d3_5_1,d3_5_2,d3_6_0,d3_6_1,d3_6_2,d3_7_0,d3_7_1,d3_7_2,d4_7_2]
  ring
#print axioms coefficient_7_2

compact_certificate_declaration theorem coefficient_7_3 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[3]?=some 0 := by
  change some (((((((d0_4_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_7_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_7_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_7_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_7_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_6_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_6_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_6_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_6_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_5_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_5_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_4_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_4_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_4_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_3_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_3_2 y z w b u))+(((d2_4_2 y z w b u)*(d3_3_1 y z w b u))+(((d2_4_3 y z w b u)*(d3_3_0 y z w b u))+0))))+((((d2_5_0 y z w b u)*(d3_2_3 y z w b u))+(((d2_5_1 y z w b u)*(d3_2_2 y z w b u))+(((d2_5_2 y z w b u)*(d3_2_1 y z w b u))+(((d2_5_3 y z w b u)*(d3_2_0 y z w b u))+0))))+((((d2_6_0 y z w b u)*(d3_1_3 y z w b u))+(((d2_6_1 y z w b u)*(d3_1_2 y z w b u))+(((d2_6_2 y z w b u)*(d3_1_1 y z w b u))+(((d2_6_3 y z w b u)*(d3_1_0 y z w b u))+0))))+(((d2_7_0 y z w b u)*(d3_0_3 y z w b u))+(((d2_7_1 y z w b u)*(d3_0_2 y z w b u))+(((d2_7_2 y z w b u)*(d3_0_1 y z w b u))+(((d2_7_3 y z w b u)*(d3_0_0 y z w b u))+0))))))))))))+((-1)*(d4_7_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_3,d0_5_3,d0_6_2,d0_6_3,d0_7_2,d0_7_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d3_4_0,d3_4_1,d3_4_2,d3_4_3,d3_5_0,d3_5_1,d3_5_2,d3_5_3,d3_6_0,d3_6_1,d3_6_2,d3_6_3,d3_7_0,d3_7_1,d3_7_2,d3_7_3,d4_7_3]
  ring
#print axioms coefficient_7_3

compact_certificate_declaration theorem coefficient_7_4 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[4]?=some 0 := by
  change some (((((((d0_4_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_7_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_7_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_7_2 y z w b u))+(((d2_0_3 y z w b u)*(d3_7_1 y z w b u))+(((d2_0_4 y z w b u)*(d3_7_0 y z w b u))+0)))))+((((d2_1_0 y z w b u)*(d3_6_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_6_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_6_2 y z w b u))+(((d2_1_3 y z w b u)*(d3_6_1 y z w b u))+(((d2_1_4 y z w b u)*(d3_6_0 y z w b u))+0)))))+((((d2_2_0 y z w b u)*(d3_5_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_2 y z w b u))+(((d2_2_3 y z w b u)*(d3_5_1 y z w b u))+(((d2_2_4 y z w b u)*(d3_5_0 y z w b u))+0)))))+((((d2_3_0 y z w b u)*(d3_4_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_4_2 y z w b u))+(((d2_3_3 y z w b u)*(d3_4_1 y z w b u))+(((d2_3_4 y z w b u)*(d3_4_0 y z w b u))+0)))))+((((d2_4_0 y z w b u)*(d3_3_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_3_3 y z w b u))+(((d2_4_2 y z w b u)*(d3_3_2 y z w b u))+(((d2_4_3 y z w b u)*(d3_3_1 y z w b u))+(((d2_4_4 y z w b u)*(d3_3_0 y z w b u))+0)))))+((((d2_5_0 y z w b u)*(d3_2_4 y z w b u))+(((d2_5_1 y z w b u)*(d3_2_3 y z w b u))+(((d2_5_2 y z w b u)*(d3_2_2 y z w b u))+(((d2_5_3 y z w b u)*(d3_2_1 y z w b u))+(((d2_5_4 y z w b u)*(d3_2_0 y z w b u))+0)))))+((((d2_6_0 y z w b u)*(d3_1_4 y z w b u))+(((d2_6_1 y z w b u)*(d3_1_3 y z w b u))+(((d2_6_2 y z w b u)*(d3_1_2 y z w b u))+(((d2_6_3 y z w b u)*(d3_1_1 y z w b u))+(((d2_6_4 y z w b u)*(d3_1_0 y z w b u))+0)))))+(((d2_7_0 y z w b u)*(d3_0_4 y z w b u))+(((d2_7_1 y z w b u)*(d3_0_3 y z w b u))+(((d2_7_2 y z w b u)*(d3_0_2 y z w b u))+((d2_7_3 y z w b u)*(d3_0_1 y z w b u)))))))))))))+((-1)*(d4_7_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_4,d0_5_4,d0_6_3,d0_6_4,d0_7_3,d0_7_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d3_4_0,d3_4_1,d3_4_2,d3_4_3,d3_4_4,d3_5_0,d3_5_1,d3_5_2,d3_5_3,d3_5_4,d3_6_0,d3_6_1,d3_6_2,d3_6_3,d3_6_4,d3_7_0,d3_7_1,d3_7_2,d3_7_3,d3_7_4,d4_7_4]
  ring
#print axioms coefficient_7_4

compact_certificate_declaration theorem coefficient_7_5 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[5]?=some 0 := by
  change some (((((((d0_4_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_7_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_7_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_7_3 y z w b u))+(((d2_0_3 y z w b u)*(d3_7_2 y z w b u))+(((d2_0_4 y z w b u)*(d3_7_1 y z w b u))+(((d2_0_5 y z w b u)*(d3_7_0 y z w b u))+0))))))+((((d2_1_0 y z w b u)*(d3_6_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_6_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_6_3 y z w b u))+(((d2_1_3 y z w b u)*(d3_6_2 y z w b u))+(((d2_1_4 y z w b u)*(d3_6_1 y z w b u))+(((d2_1_5 y z w b u)*(d3_6_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_5_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_3 y z w b u))+(((d2_2_3 y z w b u)*(d3_5_2 y z w b u))+(((d2_2_4 y z w b u)*(d3_5_1 y z w b u))+(((d2_2_5 y z w b u)*(d3_5_0 y z w b u))+0))))))+((((d2_3_0 y z w b u)*(d3_4_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_4_3 y z w b u))+(((d2_3_3 y z w b u)*(d3_4_2 y z w b u))+(((d2_3_4 y z w b u)*(d3_4_1 y z w b u))+(((d2_3_5 y z w b u)*(d3_4_0 y z w b u))+0))))))+((((d2_4_0 y z w b u)*(d3_3_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_3_4 y z w b u))+(((d2_4_2 y z w b u)*(d3_3_3 y z w b u))+(((d2_4_3 y z w b u)*(d3_3_2 y z w b u))+(((d2_4_4 y z w b u)*(d3_3_1 y z w b u))+(((d2_4_5 y z w b u)*(d3_3_0 y z w b u))+0))))))+((((d2_5_0 y z w b u)*(d3_2_5 y z w b u))+(((d2_5_1 y z w b u)*(d3_2_4 y z w b u))+(((d2_5_2 y z w b u)*(d3_2_3 y z w b u))+(((d2_5_3 y z w b u)*(d3_2_2 y z w b u))+(((d2_5_4 y z w b u)*(d3_2_1 y z w b u))+(((d2_5_5 y z w b u)*(d3_2_0 y z w b u))+0))))))+((((d2_6_0 y z w b u)*(d3_1_5 y z w b u))+(((d2_6_1 y z w b u)*(d3_1_4 y z w b u))+(((d2_6_2 y z w b u)*(d3_1_3 y z w b u))+(((d2_6_3 y z w b u)*(d3_1_2 y z w b u))+((d2_6_4 y z w b u)*(d3_1_1 y z w b u))))))+(((d2_7_0 y z w b u)*(d3_0_5 y z w b u))+(((d2_7_1 y z w b u)*(d3_0_4 y z w b u))+(((d2_7_2 y z w b u)*(d3_0_3 y z w b u))+((d2_7_3 y z w b u)*(d3_0_2 y z w b u)))))))))))))+((-1)*(d4_7_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_5,d0_5_5,d0_6_4,d0_6_5,d0_7_4,d0_7_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d3_4_0,d3_4_1,d3_4_2,d3_4_3,d3_4_4,d3_4_5,d3_5_0,d3_5_1,d3_5_2,d3_5_3,d3_5_4,d3_5_5,d3_6_0,d3_6_1,d3_6_2,d3_6_3,d3_6_4,d3_6_5,d3_7_0,d3_7_1,d3_7_2,d3_7_3,d3_7_4,d3_7_5,d4_7_5]
  ring
#print axioms coefficient_7_5

compact_certificate_declaration theorem coefficient_7_6 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[6]?=some 0 := by
  change some (((((((d0_4_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_7_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_7_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_7_4 y z w b u))+(((d2_0_3 y z w b u)*(d3_7_3 y z w b u))+(((d2_0_4 y z w b u)*(d3_7_2 y z w b u))+((d2_0_5 y z w b u)*(d3_7_1 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_6_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_6_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_6_4 y z w b u))+(((d2_1_3 y z w b u)*(d3_6_3 y z w b u))+(((d2_1_4 y z w b u)*(d3_6_2 y z w b u))+((d2_1_5 y z w b u)*(d3_6_1 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_5_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_4 y z w b u))+(((d2_2_3 y z w b u)*(d3_5_3 y z w b u))+(((d2_2_4 y z w b u)*(d3_5_2 y z w b u))+((d2_2_5 y z w b u)*(d3_5_1 y z w b u)))))))+((((d2_3_0 y z w b u)*(d3_4_6 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_4_4 y z w b u))+(((d2_3_3 y z w b u)*(d3_4_3 y z w b u))+(((d2_3_4 y z w b u)*(d3_4_2 y z w b u))+((d2_3_5 y z w b u)*(d3_4_1 y z w b u)))))))+((((d2_4_0 y z w b u)*(d3_3_6 y z w b u))+(((d2_4_1 y z w b u)*(d3_3_5 y z w b u))+(((d2_4_2 y z w b u)*(d3_3_4 y z w b u))+(((d2_4_3 y z w b u)*(d3_3_3 y z w b u))+(((d2_4_4 y z w b u)*(d3_3_2 y z w b u))+((d2_4_5 y z w b u)*(d3_3_1 y z w b u)))))))+((((d2_5_0 y z w b u)*(d3_2_6 y z w b u))+(((d2_5_1 y z w b u)*(d3_2_5 y z w b u))+(((d2_5_2 y z w b u)*(d3_2_4 y z w b u))+(((d2_5_3 y z w b u)*(d3_2_3 y z w b u))+(((d2_5_4 y z w b u)*(d3_2_2 y z w b u))+((d2_5_5 y z w b u)*(d3_2_1 y z w b u)))))))+((((d2_6_0 y z w b u)*(d3_1_6 y z w b u))+(((d2_6_1 y z w b u)*(d3_1_5 y z w b u))+(((d2_6_2 y z w b u)*(d3_1_4 y z w b u))+(((d2_6_3 y z w b u)*(d3_1_3 y z w b u))+((d2_6_4 y z w b u)*(d3_1_2 y z w b u))))))+(((d2_7_0 y z w b u)*(d3_0_6 y z w b u))+(((d2_7_1 y z w b u)*(d3_0_5 y z w b u))+(((d2_7_2 y z w b u)*(d3_0_4 y z w b u))+((d2_7_3 y z w b u)*(d3_0_3 y z w b u)))))))))))))+((-1)*(d4_7_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_6,d0_5_6,d0_6_5,d0_6_6,d0_7_5,d0_7_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d3_4_1,d3_4_2,d3_4_3,d3_4_4,d3_4_5,d3_4_6,d3_5_1,d3_5_2,d3_5_3,d3_5_4,d3_5_5,d3_5_6,d3_6_1,d3_6_2,d3_6_3,d3_6_4,d3_6_5,d3_6_6,d3_7_1,d3_7_2,d3_7_3,d3_7_4,d3_7_5,d3_7_6,d4_7_6]
  ring
#print axioms coefficient_7_6

compact_certificate_declaration theorem coefficient_7_7 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[7]?=some 0 := by
  change some (((((((d0_4_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_7_7 y z w b u))+(((d2_0_1 y z w b u)*(d3_7_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_7_5 y z w b u))+(((d2_0_3 y z w b u)*(d3_7_4 y z w b u))+(((d2_0_4 y z w b u)*(d3_7_3 y z w b u))+((d2_0_5 y z w b u)*(d3_7_2 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_6_7 y z w b u))+(((d2_1_1 y z w b u)*(d3_6_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_6_5 y z w b u))+(((d2_1_3 y z w b u)*(d3_6_4 y z w b u))+(((d2_1_4 y z w b u)*(d3_6_3 y z w b u))+((d2_1_5 y z w b u)*(d3_6_2 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_5_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_5 y z w b u))+(((d2_2_3 y z w b u)*(d3_5_4 y z w b u))+(((d2_2_4 y z w b u)*(d3_5_3 y z w b u))+((d2_2_5 y z w b u)*(d3_5_2 y z w b u)))))))+((((d2_3_0 y z w b u)*(d3_4_7 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_6 y z w b u))+(((d2_3_2 y z w b u)*(d3_4_5 y z w b u))+(((d2_3_3 y z w b u)*(d3_4_4 y z w b u))+(((d2_3_4 y z w b u)*(d3_4_3 y z w b u))+((d2_3_5 y z w b u)*(d3_4_2 y z w b u)))))))+((((d2_4_0 y z w b u)*(d3_3_7 y z w b u))+(((d2_4_1 y z w b u)*(d3_3_6 y z w b u))+(((d2_4_2 y z w b u)*(d3_3_5 y z w b u))+(((d2_4_3 y z w b u)*(d3_3_4 y z w b u))+(((d2_4_4 y z w b u)*(d3_3_3 y z w b u))+((d2_4_5 y z w b u)*(d3_3_2 y z w b u)))))))+((((d2_5_0 y z w b u)*(d3_2_7 y z w b u))+(((d2_5_1 y z w b u)*(d3_2_6 y z w b u))+(((d2_5_2 y z w b u)*(d3_2_5 y z w b u))+(((d2_5_3 y z w b u)*(d3_2_4 y z w b u))+(((d2_5_4 y z w b u)*(d3_2_3 y z w b u))+((d2_5_5 y z w b u)*(d3_2_2 y z w b u)))))))+((((d2_6_0 y z w b u)*(d3_1_7 y z w b u))+(((d2_6_1 y z w b u)*(d3_1_6 y z w b u))+(((d2_6_2 y z w b u)*(d3_1_5 y z w b u))+(((d2_6_3 y z w b u)*(d3_1_4 y z w b u))+((d2_6_4 y z w b u)*(d3_1_3 y z w b u))))))+(((d2_7_0 y z w b u)*(d3_0_7 y z w b u))+(((d2_7_1 y z w b u)*(d3_0_6 y z w b u))+(((d2_7_2 y z w b u)*(d3_0_5 y z w b u))+((d2_7_3 y z w b u)*(d3_0_4 y z w b u)))))))))))))+((-1)*(d4_7_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_7,d0_5_7,d0_6_6,d0_6_7,d0_7_6,d0_7_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d3_0_4,d3_0_5,d3_0_6,d3_0_7,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d3_4_2,d3_4_3,d3_4_4,d3_4_5,d3_4_6,d3_4_7,d3_5_2,d3_5_3,d3_5_4,d3_5_5,d3_5_6,d3_5_7,d3_6_2,d3_6_3,d3_6_4,d3_6_5,d3_6_6,d3_6_7,d3_7_2,d3_7_3,d3_7_4,d3_7_5,d3_7_6,d3_7_7,d4_7_7]
  ring
#print axioms coefficient_7_7

compact_certificate_declaration theorem coefficient_7_8 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[8]?=some 0 := by
  change some (((((((d0_4_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_7_8 y z w b u))+(((d2_0_1 y z w b u)*(d3_7_7 y z w b u))+(((d2_0_2 y z w b u)*(d3_7_6 y z w b u))+(((d2_0_3 y z w b u)*(d3_7_5 y z w b u))+(((d2_0_4 y z w b u)*(d3_7_4 y z w b u))+((d2_0_5 y z w b u)*(d3_7_3 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_6_8 y z w b u))+(((d2_1_1 y z w b u)*(d3_6_7 y z w b u))+(((d2_1_2 y z w b u)*(d3_6_6 y z w b u))+(((d2_1_3 y z w b u)*(d3_6_5 y z w b u))+(((d2_1_4 y z w b u)*(d3_6_4 y z w b u))+((d2_1_5 y z w b u)*(d3_6_3 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_5_8 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_7 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_6 y z w b u))+(((d2_2_3 y z w b u)*(d3_5_5 y z w b u))+(((d2_2_4 y z w b u)*(d3_5_4 y z w b u))+((d2_2_5 y z w b u)*(d3_5_3 y z w b u)))))))+((((d2_3_0 y z w b u)*(d3_4_8 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_7 y z w b u))+(((d2_3_2 y z w b u)*(d3_4_6 y z w b u))+(((d2_3_3 y z w b u)*(d3_4_5 y z w b u))+(((d2_3_4 y z w b u)*(d3_4_4 y z w b u))+((d2_3_5 y z w b u)*(d3_4_3 y z w b u)))))))+((((d2_4_0 y z w b u)*(d3_3_8 y z w b u))+(((d2_4_1 y z w b u)*(d3_3_7 y z w b u))+(((d2_4_2 y z w b u)*(d3_3_6 y z w b u))+(((d2_4_3 y z w b u)*(d3_3_5 y z w b u))+(((d2_4_4 y z w b u)*(d3_3_4 y z w b u))+((d2_4_5 y z w b u)*(d3_3_3 y z w b u)))))))+((((d2_5_0 y z w b u)*(d3_2_8 y z w b u))+(((d2_5_1 y z w b u)*(d3_2_7 y z w b u))+(((d2_5_2 y z w b u)*(d3_2_6 y z w b u))+(((d2_5_3 y z w b u)*(d3_2_5 y z w b u))+(((d2_5_4 y z w b u)*(d3_2_4 y z w b u))+((d2_5_5 y z w b u)*(d3_2_3 y z w b u)))))))+((((d2_6_0 y z w b u)*(d3_1_8 y z w b u))+(((d2_6_1 y z w b u)*(d3_1_7 y z w b u))+(((d2_6_2 y z w b u)*(d3_1_6 y z w b u))+(((d2_6_3 y z w b u)*(d3_1_5 y z w b u))+((d2_6_4 y z w b u)*(d3_1_4 y z w b u))))))+(((d2_7_0 y z w b u)*(d3_0_8 y z w b u))+(((d2_7_1 y z w b u)*(d3_0_7 y z w b u))+(((d2_7_2 y z w b u)*(d3_0_6 y z w b u))+((d2_7_3 y z w b u)*(d3_0_5 y z w b u)))))))))))))+((-1)*(d4_7_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_8,d0_5_8,d0_6_7,d0_6_8,d0_7_7,d0_7_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_0,d2_7_1,d2_7_2,d2_7_3,d3_0_5,d3_0_6,d3_0_7,d3_0_8,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d3_3_8,d3_4_3,d3_4_4,d3_4_5,d3_4_6,d3_4_7,d3_4_8,d3_5_3,d3_5_4,d3_5_5,d3_5_6,d3_5_7,d3_5_8,d3_6_3,d3_6_4,d3_6_5,d3_6_6,d3_6_7,d3_6_8,d3_7_3,d3_7_4,d3_7_5,d3_7_6,d3_7_7,d3_7_8,d4_7_8]
  ring
#print axioms coefficient_7_8
compact_certificate_declaration theorem coefficient_7_9 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[9]?=some 0 := by
  change some (((((((d0_4_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_9 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_7_9 y z w b u))+(((d2_0_1 y z w b u)*(d3_7_8 y z w b u))+(((d2_0_2 y z w b u)*(d3_7_7 y z w b u))+(((d2_0_3 y z w b u)*(d3_7_6 y z w b u))+(((d2_0_4 y z w b u)*(d3_7_5 y z w b u))+((d2_0_5 y z w b u)*(d3_7_4 y z w b u)))))))+((((d2_1_0 y z w b u)*(d3_6_9 y z w b u))+(((d2_1_1 y z w b u)*(d3_6_8 y z w b u))+(((d2_1_2 y z w b u)*(d3_6_7 y z w b u))+(((d2_1_3 y z w b u)*(d3_6_6 y z w b u))+(((d2_1_4 y z w b u)*(d3_6_5 y z w b u))+((d2_1_5 y z w b u)*(d3_6_4 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_5_9 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_8 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_7 y z w b u))+(((d2_2_3 y z w b u)*(d3_5_6 y z w b u))+(((d2_2_4 y z w b u)*(d3_5_5 y z w b u))+((d2_2_5 y z w b u)*(d3_5_4 y z w b u)))))))+((((d2_3_0 y z w b u)*(d3_4_9 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_8 y z w b u))+(((d2_3_2 y z w b u)*(d3_4_7 y z w b u))+(((d2_3_3 y z w b u)*(d3_4_6 y z w b u))+(((d2_3_4 y z w b u)*(d3_4_5 y z w b u))+((d2_3_5 y z w b u)*(d3_4_4 y z w b u)))))))+((((d2_4_0 y z w b u)*(d3_3_9 y z w b u))+(((d2_4_1 y z w b u)*(d3_3_8 y z w b u))+(((d2_4_2 y z w b u)*(d3_3_7 y z w b u))+(((d2_4_3 y z w b u)*(d3_3_6 y z w b u))+(((d2_4_4 y z w b u)*(d3_3_5 y z w b u))+((d2_4_5 y z w b u)*(d3_3_4 y z w b u)))))))+((((d2_5_0 y z w b u)*(d3_2_9 y z w b u))+(((d2_5_1 y z w b u)*(d3_2_8 y z w b u))+(((d2_5_2 y z w b u)*(d3_2_7 y z w b u))+(((d2_5_3 y z w b u)*(d3_2_6 y z w b u))+(((d2_5_4 y z w b u)*(d3_2_5 y z w b u))+((d2_5_5 y z w b u)*(d3_2_4 y z w b u)))))))+((((d2_6_0 y z w b u)*(d3_1_9 y z w b u))+(((d2_6_1 y z w b u)*(d3_1_8 y z w b u))+(((d2_6_2 y z w b u)*(d3_1_7 y z w b u))+(((d2_6_3 y z w b u)*(d3_1_6 y z w b u))+((d2_6_4 y z w b u)*(d3_1_5 y z w b u))))))+(((d2_7_1 y z w b u)*(d3_0_8 y z w b u))+(((d2_7_2 y z w b u)*(d3_0_7 y z w b u))+((d2_7_3 y z w b u)*(d3_0_6 y z w b u))))))))))))+((-1)*(d4_7_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_9,d0_5_9,d0_6_8,d0_6_9,d0_7_8,d0_7_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_0,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_0,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_0,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_1,d2_7_2,d2_7_3,d3_0_6,d3_0_7,d3_0_8,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_1_9,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_2_9,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d3_3_8,d3_3_9,d3_4_4,d3_4_5,d3_4_6,d3_4_7,d3_4_8,d3_4_9,d3_5_4,d3_5_5,d3_5_6,d3_5_7,d3_5_8,d3_5_9,d3_6_4,d3_6_5,d3_6_6,d3_6_7,d3_6_8,d3_6_9,d3_7_4,d3_7_5,d3_7_6,d3_7_7,d3_7_8,d3_7_9,d4_7_9]
  ring
#print axioms coefficient_7_9

compact_certificate_declaration theorem coefficient_7_10 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[10]?=some 0 := by
  change some (((((((d0_4_10 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_10 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_9 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_10 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_9 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_10 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_7_9 y z w b u))+(((d2_0_2 y z w b u)*(d3_7_8 y z w b u))+(((d2_0_3 y z w b u)*(d3_7_7 y z w b u))+(((d2_0_4 y z w b u)*(d3_7_6 y z w b u))+((d2_0_5 y z w b u)*(d3_7_5 y z w b u))))))+((((d2_1_1 y z w b u)*(d3_6_9 y z w b u))+(((d2_1_2 y z w b u)*(d3_6_8 y z w b u))+(((d2_1_3 y z w b u)*(d3_6_7 y z w b u))+(((d2_1_4 y z w b u)*(d3_6_6 y z w b u))+((d2_1_5 y z w b u)*(d3_6_5 y z w b u))))))+((((d2_2_1 y z w b u)*(d3_5_9 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_8 y z w b u))+(((d2_2_3 y z w b u)*(d3_5_7 y z w b u))+(((d2_2_4 y z w b u)*(d3_5_6 y z w b u))+((d2_2_5 y z w b u)*(d3_5_5 y z w b u))))))+((((d2_3_1 y z w b u)*(d3_4_9 y z w b u))+(((d2_3_2 y z w b u)*(d3_4_8 y z w b u))+(((d2_3_3 y z w b u)*(d3_4_7 y z w b u))+(((d2_3_4 y z w b u)*(d3_4_6 y z w b u))+((d2_3_5 y z w b u)*(d3_4_5 y z w b u))))))+((((d2_4_1 y z w b u)*(d3_3_9 y z w b u))+(((d2_4_2 y z w b u)*(d3_3_8 y z w b u))+(((d2_4_3 y z w b u)*(d3_3_7 y z w b u))+(((d2_4_4 y z w b u)*(d3_3_6 y z w b u))+((d2_4_5 y z w b u)*(d3_3_5 y z w b u))))))+((((d2_5_1 y z w b u)*(d3_2_9 y z w b u))+(((d2_5_2 y z w b u)*(d3_2_8 y z w b u))+(((d2_5_3 y z w b u)*(d3_2_7 y z w b u))+(((d2_5_4 y z w b u)*(d3_2_6 y z w b u))+((d2_5_5 y z w b u)*(d3_2_5 y z w b u))))))+((((d2_6_1 y z w b u)*(d3_1_9 y z w b u))+(((d2_6_2 y z w b u)*(d3_1_8 y z w b u))+(((d2_6_3 y z w b u)*(d3_1_7 y z w b u))+((d2_6_4 y z w b u)*(d3_1_6 y z w b u)))))+(((d2_7_2 y z w b u)*(d3_0_8 y z w b u))+((d2_7_3 y z w b u)*(d3_0_7 y z w b u)))))))))))+((-1)*(d4_7_10 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_10,d0_5_10,d0_6_10,d0_6_9,d0_7_10,d0_7_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_1,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_1,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_1,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_1,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_1,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_1,d2_6_2,d2_6_3,d2_6_4,d2_7_2,d2_7_3,d3_0_7,d3_0_8,d3_1_6,d3_1_7,d3_1_8,d3_1_9,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_2_9,d3_3_5,d3_3_6,d3_3_7,d3_3_8,d3_3_9,d3_4_5,d3_4_6,d3_4_7,d3_4_8,d3_4_9,d3_5_5,d3_5_6,d3_5_7,d3_5_8,d3_5_9,d3_6_5,d3_6_6,d3_6_7,d3_6_8,d3_6_9,d3_7_5,d3_7_6,d3_7_7,d3_7_8,d3_7_9,d4_7_10]
  ring
#print axioms coefficient_7_10
compact_certificate_declaration theorem coefficient_7_11 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[11]?=some 0 := by
  change some (((((((d0_4_11 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_11 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_10 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_11 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_10 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_11 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_7_9 y z w b u))+(((d2_0_3 y z w b u)*(d3_7_8 y z w b u))+(((d2_0_4 y z w b u)*(d3_7_7 y z w b u))+((d2_0_5 y z w b u)*(d3_7_6 y z w b u)))))+((((d2_1_2 y z w b u)*(d3_6_9 y z w b u))+(((d2_1_3 y z w b u)*(d3_6_8 y z w b u))+(((d2_1_4 y z w b u)*(d3_6_7 y z w b u))+((d2_1_5 y z w b u)*(d3_6_6 y z w b u)))))+((((d2_2_2 y z w b u)*(d3_5_9 y z w b u))+(((d2_2_3 y z w b u)*(d3_5_8 y z w b u))+(((d2_2_4 y z w b u)*(d3_5_7 y z w b u))+((d2_2_5 y z w b u)*(d3_5_6 y z w b u)))))+((((d2_3_2 y z w b u)*(d3_4_9 y z w b u))+(((d2_3_3 y z w b u)*(d3_4_8 y z w b u))+(((d2_3_4 y z w b u)*(d3_4_7 y z w b u))+((d2_3_5 y z w b u)*(d3_4_6 y z w b u)))))+((((d2_4_2 y z w b u)*(d3_3_9 y z w b u))+(((d2_4_3 y z w b u)*(d3_3_8 y z w b u))+(((d2_4_4 y z w b u)*(d3_3_7 y z w b u))+((d2_4_5 y z w b u)*(d3_3_6 y z w b u)))))+((((d2_5_2 y z w b u)*(d3_2_9 y z w b u))+(((d2_5_3 y z w b u)*(d3_2_8 y z w b u))+(((d2_5_4 y z w b u)*(d3_2_7 y z w b u))+((d2_5_5 y z w b u)*(d3_2_6 y z w b u)))))+((((d2_6_2 y z w b u)*(d3_1_9 y z w b u))+(((d2_6_3 y z w b u)*(d3_1_8 y z w b u))+((d2_6_4 y z w b u)*(d3_1_7 y z w b u))))+((d2_7_3 y z w b u)*(d3_0_8 y z w b u))))))))))+((-1)*(d4_7_11 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_11,d0_5_11,d0_6_10,d0_6_11,d0_7_10,d0_7_11,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_0_4,d2_0_5,d2_1_2,d2_1_3,d2_1_4,d2_1_5,d2_2_2,d2_2_3,d2_2_4,d2_2_5,d2_3_2,d2_3_3,d2_3_4,d2_3_5,d2_4_2,d2_4_3,d2_4_4,d2_4_5,d2_5_2,d2_5_3,d2_5_4,d2_5_5,d2_6_2,d2_6_3,d2_6_4,d2_7_3,d3_0_8,d3_1_7,d3_1_8,d3_1_9,d3_2_6,d3_2_7,d3_2_8,d3_2_9,d3_3_6,d3_3_7,d3_3_8,d3_3_9,d3_4_6,d3_4_7,d3_4_8,d3_4_9,d3_5_6,d3_5_7,d3_5_8,d3_5_9,d3_6_6,d3_6_7,d3_6_8,d3_6_9,d3_7_6,d3_7_7,d3_7_8,d3_7_9,d4_7_11]
  ring
#print axioms coefficient_7_11
compact_certificate_declaration theorem coefficient_7_12 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[12]?=some 0 := by
  change some ((((((d0_4_12 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_12 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_11 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_12 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_11 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_12 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_3 y z w b u)*(d3_7_9 y z w b u))+(((d2_0_4 y z w b u)*(d3_7_8 y z w b u))+((d2_0_5 y z w b u)*(d3_7_7 y z w b u))))+((((d2_1_3 y z w b u)*(d3_6_9 y z w b u))+(((d2_1_4 y z w b u)*(d3_6_8 y z w b u))+((d2_1_5 y z w b u)*(d3_6_7 y z w b u))))+((((d2_2_3 y z w b u)*(d3_5_9 y z w b u))+(((d2_2_4 y z w b u)*(d3_5_8 y z w b u))+((d2_2_5 y z w b u)*(d3_5_7 y z w b u))))+((((d2_3_3 y z w b u)*(d3_4_9 y z w b u))+(((d2_3_4 y z w b u)*(d3_4_8 y z w b u))+((d2_3_5 y z w b u)*(d3_4_7 y z w b u))))+((((d2_4_3 y z w b u)*(d3_3_9 y z w b u))+(((d2_4_4 y z w b u)*(d3_3_8 y z w b u))+((d2_4_5 y z w b u)*(d3_3_7 y z w b u))))+((((d2_5_3 y z w b u)*(d3_2_9 y z w b u))+(((d2_5_4 y z w b u)*(d3_2_8 y z w b u))+((d2_5_5 y z w b u)*(d3_2_7 y z w b u))))+(((d2_6_3 y z w b u)*(d3_1_9 y z w b u))+((d2_6_4 y z w b u)*(d3_1_8 y z w b u)))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_12,d0_5_12,d0_6_11,d0_6_12,d0_7_11,d0_7_12,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_0_4,d2_0_5,d2_1_3,d2_1_4,d2_1_5,d2_2_3,d2_2_4,d2_2_5,d2_3_3,d2_3_4,d2_3_5,d2_4_3,d2_4_4,d2_4_5,d2_5_3,d2_5_4,d2_5_5,d2_6_3,d2_6_4,d3_1_8,d3_1_9,d3_2_7,d3_2_8,d3_2_9,d3_3_7,d3_3_8,d3_3_9,d3_4_7,d3_4_8,d3_4_9,d3_5_7,d3_5_8,d3_5_9,d3_6_7,d3_6_8,d3_6_9,d3_7_7,d3_7_8,d3_7_9]
  ring
#print axioms coefficient_7_12

compact_certificate_declaration theorem coefficient_7_13 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[13]?=some 0 := by
  change some ((((((d0_4_13 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_13 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_12 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_13 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_12 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_13 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_4 y z w b u)*(d3_7_9 y z w b u))+((d2_0_5 y z w b u)*(d3_7_8 y z w b u)))+((((d2_1_4 y z w b u)*(d3_6_9 y z w b u))+((d2_1_5 y z w b u)*(d3_6_8 y z w b u)))+((((d2_2_4 y z w b u)*(d3_5_9 y z w b u))+((d2_2_5 y z w b u)*(d3_5_8 y z w b u)))+((((d2_3_4 y z w b u)*(d3_4_9 y z w b u))+((d2_3_5 y z w b u)*(d3_4_8 y z w b u)))+((((d2_4_4 y z w b u)*(d3_3_9 y z w b u))+((d2_4_5 y z w b u)*(d3_3_8 y z w b u)))+((((d2_5_4 y z w b u)*(d3_2_9 y z w b u))+((d2_5_5 y z w b u)*(d3_2_8 y z w b u)))+((d2_6_4 y z w b u)*(d3_1_9 y z w b u))))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_13,d0_5_13,d0_6_12,d0_6_13,d0_7_12,d0_7_13,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_4,d2_0_5,d2_1_4,d2_1_5,d2_2_4,d2_2_5,d2_3_4,d2_3_5,d2_4_4,d2_4_5,d2_5_4,d2_5_5,d2_6_4,d3_1_9,d3_2_8,d3_2_9,d3_3_8,d3_3_9,d3_4_8,d3_4_9,d3_5_8,d3_5_9,d3_6_8,d3_6_9,d3_7_8,d3_7_9]
  ring
#print axioms coefficient_7_13
compact_certificate_declaration theorem coefficient_7_14 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[14]?=some 0 := by
  change some (((((d0_6_13 y z w b u)*(d1_1_1 y z w b u))+((d0_7_13 y z w b u)*(d1_0_1 y z w b u)))+(((d2_0_5 y z w b u)*(d3_7_9 y z w b u))+(((d2_1_5 y z w b u)*(d3_6_9 y z w b u))+(((d2_2_5 y z w b u)*(d3_5_9 y z w b u))+(((d2_3_5 y z w b u)*(d3_4_9 y z w b u))+(((d2_4_5 y z w b u)*(d3_3_9 y z w b u))+((d2_5_5 y z w b u)*(d3_2_9 y z w b u)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_6_13,d0_7_13,d1_0_1,d1_1_1,d2_0_5,d2_1_5,d2_2_5,d2_3_5,d2_4_5,d2_5_5,d3_2_9,d3_3_9,d3_4_9,d3_5_9,d3_6_9,d3_7_9]
  ring
#print axioms coefficient_7_14

end SmallLevelTwentySixMMPPariTrace026
end

end

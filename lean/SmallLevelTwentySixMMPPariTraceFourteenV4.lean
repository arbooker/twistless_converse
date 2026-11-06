module
public import SmallLevelTwentySixMMPPariTraceInitialV4
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

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_length (y z w a b u : ℂ) : (certificate y z w a b u).length=25 := by
  norm_num [certificate,add,multiply,scale,coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6]

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_0 (y z w b u : ℂ) : (innerCertificate0 y z w b u).length=10 := by
  norm_num [innerCertificate0,add,multiply,scale,inner0_0,inner1_0,inner2_0,inner3_0,inner4_0]
compact_certificate_declaration theorem inner_eval_0 (y z w a b u : ℂ) :
    evaluate a (innerCertificate0 y z w b u)=(((((c0_0 y z w a b u)*(c1_0 y z w a b u))+0)+(((c2_0 y z w a b u)*(c3_0 y z w a b u))+0))+((-1)*(c4_0 y z w a b u))) := by
  simp only [innerCertificate0,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_0,c1_0,c2_0,c3_0,c4_0]
#print axioms inner_eval_0

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
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
  change some (((((d0_0_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_0_4 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_0 y z w b u)*(d3_0_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_0_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_0_2 y z w b u))+((d2_0_3 y z w b u)*(d3_0_1 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_3,d0_0_4,d1_0_0,d1_0_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d3_0_1,d3_0_2,d3_0_3,d3_0_4]
  ring
#print axioms coefficient_0_4
compact_certificate_declaration theorem coefficient_0_5 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[5]?=some 0 := by
  change some (((((d0_0_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_0_5 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_0 y z w b u)*(d3_0_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_0_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_0_3 y z w b u))+((d2_0_3 y z w b u)*(d3_0_2 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_4,d0_0_5,d1_0_0,d1_0_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d3_0_2,d3_0_3,d3_0_4,d3_0_5]
  ring
#print axioms coefficient_0_5

compact_certificate_declaration theorem coefficient_0_6 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[6]?=some 0 := by
  change some (((((d0_0_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_0_6 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_0 y z w b u)*(d3_0_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_0_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_0_4 y z w b u))+((d2_0_3 y z w b u)*(d3_0_3 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_5,d0_0_6,d1_0_0,d1_0_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d3_0_3,d3_0_4,d3_0_5,d3_0_6]
  ring
#print axioms coefficient_0_6
compact_certificate_declaration theorem coefficient_0_7 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[7]?=some 0 := by
  change some (((((d0_0_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_0_7 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_1 y z w b u)*(d3_0_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_0_5 y z w b u))+((d2_0_3 y z w b u)*(d3_0_4 y z w b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_6,d0_0_7,d1_0_0,d1_0_1,d2_0_1,d2_0_2,d2_0_3,d3_0_4,d3_0_5,d3_0_6]
  ring
#print axioms coefficient_0_7
compact_certificate_declaration theorem coefficient_0_8 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[8]?=some 0 := by
  change some (((((d0_0_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_0_8 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_2 y z w b u)*(d3_0_6 y z w b u))+((d2_0_3 y z w b u)*(d3_0_5 y z w b u)))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_7,d0_0_8,d1_0_0,d1_0_1,d2_0_2,d2_0_3,d3_0_5,d3_0_6]
  ring
#print axioms coefficient_0_8

compact_certificate_declaration theorem coefficient_0_9 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[9]?=some 0 := by
  change some ((((d0_0_8 y z w b u)*(d1_0_1 y z w b u))+((d2_0_3 y z w b u)*(d3_0_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_8,d1_0_1,d2_0_3,d3_0_6]
  ring
#print axioms coefficient_0_9

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_1 (y z w b u : ℂ) : (innerCertificate1 y z w b u).length=12 := by
  norm_num [innerCertificate1,add,multiply,scale,inner0_0,inner0_1,inner1_0,inner1_1,inner2_0,inner2_1,inner3_0,inner3_1,inner4_1]
compact_certificate_declaration theorem inner_eval_1 (y z w a b u : ℂ) :
    evaluate a (innerCertificate1 y z w b u)=(((((c0_0 y z w a b u)*(c1_1 y z w a b u))+(((c0_1 y z w a b u)*(c1_0 y z w a b u))+0))+(((c2_0 y z w a b u)*(c3_1 y z w a b u))+(((c2_1 y z w a b u)*(c3_0 y z w a b u))+0)))+((-1)*(c4_1 y z w a b u))) := by
  simp only [innerCertificate1,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_0,c0_1,c1_0,c1_1,c2_0,c2_1,c3_0,c3_1,c4_1]
#print axioms inner_eval_1

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
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
  change some ((((((d0_0_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_0_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_1_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_4 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_0 y z w b u)*(d3_1_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_1_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_1_2 y z w b u))+((d2_0_3 y z w b u)*(d3_1_1 y z w b u)))))+(((d2_1_0 y z w b u)*(d3_0_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_0_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_0_2 y z w b u))+((d2_1_3 y z w b u)*(d3_0_1 y z w b u))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_3,d0_0_4,d0_1_3,d0_1_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_1_1,d3_1_2,d3_1_3,d3_1_4]
  ring
#print axioms coefficient_1_4
compact_certificate_declaration theorem coefficient_1_5 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[5]?=some 0 := by
  change some ((((((d0_0_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_0_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_1_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_5 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_0 y z w b u)*(d3_1_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_1_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_1_3 y z w b u))+((d2_0_3 y z w b u)*(d3_1_2 y z w b u)))))+(((d2_1_0 y z w b u)*(d3_0_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_0_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_0_3 y z w b u))+((d2_1_3 y z w b u)*(d3_0_2 y z w b u))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_4,d0_0_5,d0_1_4,d0_1_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_1_2,d3_1_3,d3_1_4,d3_1_5]
  ring
#print axioms coefficient_1_5

compact_certificate_declaration theorem coefficient_1_6 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[6]?=some 0 := by
  change some ((((((d0_0_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_0_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_1_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_6 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_0 y z w b u)*(d3_1_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_1_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_1_4 y z w b u))+((d2_0_3 y z w b u)*(d3_1_3 y z w b u)))))+(((d2_1_0 y z w b u)*(d3_0_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_0_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_0_4 y z w b u))+((d2_1_3 y z w b u)*(d3_0_3 y z w b u))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_5,d0_0_6,d0_1_5,d0_1_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_1_3,d3_1_4,d3_1_5,d3_1_6]
  ring
#print axioms coefficient_1_6
compact_certificate_declaration theorem coefficient_1_7 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[7]?=some 0 := by
  change some ((((((d0_0_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_0_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_1_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_7 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_0 y z w b u)*(d3_1_7 y z w b u))+(((d2_0_1 y z w b u)*(d3_1_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_1_5 y z w b u))+((d2_0_3 y z w b u)*(d3_1_4 y z w b u)))))+(((d2_1_1 y z w b u)*(d3_0_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_0_5 y z w b u))+((d2_1_3 y z w b u)*(d3_0_4 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_6,d0_0_7,d0_1_6,d0_1_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_1,d2_1_2,d2_1_3,d3_0_4,d3_0_5,d3_0_6,d3_1_4,d3_1_5,d3_1_6,d3_1_7]
  ring
#print axioms coefficient_1_7
compact_certificate_declaration theorem coefficient_1_8 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[8]?=some 0 := by
  change some ((((((d0_0_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_0_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_1_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_8 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_0 y z w b u)*(d3_1_8 y z w b u))+(((d2_0_1 y z w b u)*(d3_1_7 y z w b u))+(((d2_0_2 y z w b u)*(d3_1_6 y z w b u))+((d2_0_3 y z w b u)*(d3_1_5 y z w b u)))))+(((d2_1_2 y z w b u)*(d3_0_6 y z w b u))+((d2_1_3 y z w b u)*(d3_0_5 y z w b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_7,d0_0_8,d0_1_7,d0_1_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_2,d2_1_3,d3_0_5,d3_0_6,d3_1_5,d3_1_6,d3_1_7,d3_1_8]
  ring
#print axioms coefficient_1_8

compact_certificate_declaration theorem coefficient_1_9 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[9]?=some 0 := by
  change some (((((d0_0_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_9 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_1 y z w b u)*(d3_1_8 y z w b u))+(((d2_0_2 y z w b u)*(d3_1_7 y z w b u))+((d2_0_3 y z w b u)*(d3_1_6 y z w b u))))+((d2_1_3 y z w b u)*(d3_0_6 y z w b u)))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_8,d0_1_8,d0_1_9,d1_0_0,d1_0_1,d1_1_1,d2_0_1,d2_0_2,d2_0_3,d2_1_3,d3_0_6,d3_1_6,d3_1_7,d3_1_8]
  ring
#print axioms coefficient_1_9
compact_certificate_declaration theorem coefficient_1_10 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[10]?=some 0 := by
  change some (((((d0_1_9 y z w b u)*(d1_0_1 y z w b u))+(((d0_1_10 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_0_2 y z w b u)*(d3_1_8 y z w b u))+((d2_0_3 y z w b u)*(d3_1_7 y z w b u)))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_10,d0_1_9,d1_0_0,d1_0_1,d2_0_2,d2_0_3,d3_1_7,d3_1_8]
  ring
#print axioms coefficient_1_10
compact_certificate_declaration theorem coefficient_1_11 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[11]?=some 0 := by
  change some ((((d0_1_10 y z w b u)*(d1_0_1 y z w b u))+((d2_0_3 y z w b u)*(d3_1_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_10,d1_0_1,d2_0_3,d3_1_8]
  ring
#print axioms coefficient_1_11

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_2 (y z w b u : ℂ) : (innerCertificate2 y z w b u).length=12 := by
  norm_num [innerCertificate2,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner1_0,inner1_1,inner1_2,inner2_0,inner2_1,inner2_2,inner3_0,inner3_1,inner3_2,inner4_2]
compact_certificate_declaration theorem inner_eval_2 (y z w a b u : ℂ) :
    evaluate a (innerCertificate2 y z w b u)=(((((c0_0 y z w a b u)*(c1_2 y z w a b u))+(((c0_1 y z w a b u)*(c1_1 y z w a b u))+(((c0_2 y z w a b u)*(c1_0 y z w a b u))+0)))+(((c2_0 y z w a b u)*(c3_2 y z w a b u))+(((c2_1 y z w a b u)*(c3_1 y z w a b u))+(((c2_2 y z w a b u)*(c3_0 y z w a b u))+0))))+((-1)*(c4_2 y z w a b u))) := by
  simp only [innerCertificate2,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_0,c0_1,c0_2,c1_0,c1_1,c1_2,c2_0,c2_1,c2_2,c3_0,c3_1,c3_2,c4_2]
#print axioms inner_eval_2

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
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
  change some ((((((d0_0_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_4 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_2_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_2_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_2_2 y z w b u))+((d2_0_3 y z w b u)*(d3_2_1 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_1_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_1_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_1_2 y z w b u))+((d2_1_3 y z w b u)*(d3_1_1 y z w b u)))))+(((d2_2_0 y z w b u)*(d3_0_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_0_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_0_2 y z w b u))+((d2_2_3 y z w b u)*(d3_0_1 y z w b u)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_4,d0_1_3,d0_1_4,d0_2_3,d0_2_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_2_1,d3_2_2,d3_2_3,d3_2_4]
  ring
#print axioms coefficient_2_4
compact_certificate_declaration theorem coefficient_2_5 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[5]?=some 0 := by
  change some ((((((d0_0_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_5 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_2_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_2_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_2_3 y z w b u))+((d2_0_3 y z w b u)*(d3_2_2 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_1_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_1_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_1_3 y z w b u))+((d2_1_3 y z w b u)*(d3_1_2 y z w b u)))))+(((d2_2_0 y z w b u)*(d3_0_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_0_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_0_3 y z w b u))+((d2_2_3 y z w b u)*(d3_0_2 y z w b u)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_5,d0_1_4,d0_1_5,d0_2_4,d0_2_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_2_2,d3_2_3,d3_2_4,d3_2_5]
  ring
#print axioms coefficient_2_5

compact_certificate_declaration theorem coefficient_2_6 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[6]?=some 0 := by
  change some ((((((d0_0_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_6 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_2_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_2_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_2_4 y z w b u))+((d2_0_3 y z w b u)*(d3_2_3 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_1_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_1_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_1_4 y z w b u))+((d2_1_3 y z w b u)*(d3_1_3 y z w b u)))))+(((d2_2_0 y z w b u)*(d3_0_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_0_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_0_4 y z w b u))+((d2_2_3 y z w b u)*(d3_0_3 y z w b u)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_6,d0_1_5,d0_1_6,d0_2_5,d0_2_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_2_3,d3_2_4,d3_2_5,d3_2_6]
  ring
#print axioms coefficient_2_6
compact_certificate_declaration theorem coefficient_2_7 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[7]?=some 0 := by
  change some ((((((d0_0_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_7 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_2_7 y z w b u))+(((d2_0_1 y z w b u)*(d3_2_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_2_5 y z w b u))+((d2_0_3 y z w b u)*(d3_2_4 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_1_7 y z w b u))+(((d2_1_1 y z w b u)*(d3_1_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_1_5 y z w b u))+((d2_1_3 y z w b u)*(d3_1_4 y z w b u)))))+(((d2_2_1 y z w b u)*(d3_0_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_0_5 y z w b u))+((d2_2_3 y z w b u)*(d3_0_4 y z w b u))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_7,d0_1_6,d0_1_7,d0_2_6,d0_2_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d3_0_4,d3_0_5,d3_0_6,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_2_4,d3_2_5,d3_2_6,d3_2_7]
  ring
#print axioms coefficient_2_7
compact_certificate_declaration theorem coefficient_2_8 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[8]?=some 0 := by
  change some ((((((d0_0_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_1_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_8 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_2_8 y z w b u))+(((d2_0_1 y z w b u)*(d3_2_7 y z w b u))+(((d2_0_2 y z w b u)*(d3_2_6 y z w b u))+((d2_0_3 y z w b u)*(d3_2_5 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_1_8 y z w b u))+(((d2_1_1 y z w b u)*(d3_1_7 y z w b u))+(((d2_1_2 y z w b u)*(d3_1_6 y z w b u))+((d2_1_3 y z w b u)*(d3_1_5 y z w b u)))))+(((d2_2_2 y z w b u)*(d3_0_6 y z w b u))+((d2_2_3 y z w b u)*(d3_0_5 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_8,d0_1_7,d0_1_8,d0_2_7,d0_2_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_2,d2_2_3,d3_0_5,d3_0_6,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_2_5,d3_2_6,d3_2_7,d3_2_8]
  ring
#print axioms coefficient_2_8

compact_certificate_declaration theorem coefficient_2_9 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[9]?=some 0 := by
  change some ((((((d0_1_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_9 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_1 y z w b u)*(d3_2_8 y z w b u))+(((d2_0_2 y z w b u)*(d3_2_7 y z w b u))+((d2_0_3 y z w b u)*(d3_2_6 y z w b u))))+((((d2_1_1 y z w b u)*(d3_1_8 y z w b u))+(((d2_1_2 y z w b u)*(d3_1_7 y z w b u))+((d2_1_3 y z w b u)*(d3_1_6 y z w b u))))+((d2_2_3 y z w b u)*(d3_0_6 y z w b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_8,d0_1_9,d0_2_8,d0_2_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_1,d2_0_2,d2_0_3,d2_1_1,d2_1_2,d2_1_3,d2_2_3,d3_0_6,d3_1_6,d3_1_7,d3_1_8,d3_2_6,d3_2_7,d3_2_8]
  ring
#print axioms coefficient_2_9
compact_certificate_declaration theorem coefficient_2_10 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[10]?=some 0 := by
  change some ((((((d0_1_9 y z w b u)*(d1_1_1 y z w b u))+(((d0_1_10 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_2_9 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_10 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_0_2 y z w b u)*(d3_2_8 y z w b u))+((d2_0_3 y z w b u)*(d3_2_7 y z w b u)))+(((d2_1_2 y z w b u)*(d3_1_8 y z w b u))+((d2_1_3 y z w b u)*(d3_1_7 y z w b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_10,d0_1_9,d0_2_10,d0_2_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_0_2,d2_0_3,d2_1_2,d2_1_3,d3_1_7,d3_1_8,d3_2_7,d3_2_8]
  ring
#print axioms coefficient_2_10
compact_certificate_declaration theorem coefficient_2_11 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[11]?=some 0 := by
  change some (((((d0_1_10 y z w b u)*(d1_1_1 y z w b u))+((d0_2_10 y z w b u)*(d1_0_1 y z w b u)))+(((d2_0_3 y z w b u)*(d3_2_8 y z w b u))+((d2_1_3 y z w b u)*(d3_1_8 y z w b u)))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_10,d0_2_10,d1_0_1,d1_1_1,d2_0_3,d2_1_3,d3_1_8,d3_2_8]
  ring
#print axioms coefficient_2_11

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_3 (y z w b u : ℂ) : (innerCertificate3 y z w b u).length=12 := by
  norm_num [innerCertificate3,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner0_3,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner3_0,inner3_1,inner3_2,inner3_3,inner4_3]
compact_certificate_declaration theorem inner_eval_3 (y z w a b u : ℂ) :
    evaluate a (innerCertificate3 y z w b u)=(((((c0_0 y z w a b u)*(c1_3 y z w a b u))+(((c0_1 y z w a b u)*(c1_2 y z w a b u))+(((c0_2 y z w a b u)*(c1_1 y z w a b u))+(((c0_3 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_3 y z w a b u))+(((c2_1 y z w a b u)*(c3_2 y z w a b u))+(((c2_2 y z w a b u)*(c3_1 y z w a b u))+(((c2_3 y z w a b u)*(c3_0 y z w a b u))+0)))))+((-1)*(c4_3 y z w a b u))) := by
  simp only [innerCertificate3,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_0,c0_1,c0_2,c0_3,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c3_0,c3_1,c3_2,c3_3,c4_3]
#print axioms inner_eval_3

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_3_0 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[0]?=some 0 := by
  change some (((((((d0_0_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_3_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_3_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_2_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_1_0 y z w b u))+0)+(((d2_3_0 y z w b u)*(d3_0_0 y z w b u))+0)))))+(((-1)*(d4_3_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_1_0,d0_2_0,d0_3_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_1_0,d2_2_0,d2_3_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d4_3_0]
  ring
#print axioms coefficient_3_0
compact_certificate_declaration theorem coefficient_3_1 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[1]?=some 0 := by
  change some (((((((d0_0_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_3_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_3_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_2_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_2_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_1_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_0 y z w b u))+0))+(((d2_3_0 y z w b u)*(d3_0_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_0_0 y z w b u))+0))))))+((-1)*(d4_3_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_1,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d0_3_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d3_0_0,d3_0_1,d3_1_0,d3_1_1,d3_2_0,d3_2_1,d3_3_0,d3_3_1,d4_3_1]
  ring
#print axioms coefficient_3_1
compact_certificate_declaration theorem coefficient_3_2 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[2]?=some 0 := by
  change some (((((((d0_0_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_3_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_3_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_3_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_2_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_2_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_2_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_1_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_0 y z w b u))+0)))+(((d2_3_0 y z w b u)*(d3_0_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_0_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_0_0 y z w b u))+0)))))))+((-1)*(d4_3_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_2,d0_1_2,d0_2_1,d0_2_2,d0_3_1,d0_3_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d3_0_0,d3_0_1,d3_0_2,d3_1_0,d3_1_1,d3_1_2,d3_2_0,d3_2_1,d3_2_2,d3_3_0,d3_3_1,d3_3_2,d4_3_2]
  ring
#print axioms coefficient_3_2

compact_certificate_declaration theorem coefficient_3_3 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[3]?=some 0 := by
  change some (((((((d0_0_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_3_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_3_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_3_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_3_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_2_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_2_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_2_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_2_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_1_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_1_0 y z w b u))+0))))+(((d2_3_0 y z w b u)*(d3_0_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_0_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_0_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_0_0 y z w b u))+0))))))))+((-1)*(d4_3_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_3,d0_1_3,d0_2_2,d0_2_3,d0_3_2,d0_3_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d3_0_0,d3_0_1,d3_0_2,d3_0_3,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d4_3_3]
  ring
#print axioms coefficient_3_3
compact_certificate_declaration theorem coefficient_3_4 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[4]?=some 0 := by
  change some (((((((d0_0_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_3_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_3_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_3_2 y z w b u))+((d2_0_3 y z w b u)*(d3_3_1 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_2_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_2_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_2_2 y z w b u))+((d2_1_3 y z w b u)*(d3_2_1 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_1_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_2 y z w b u))+((d2_2_3 y z w b u)*(d3_1_1 y z w b u)))))+(((d2_3_0 y z w b u)*(d3_0_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_0_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_0_2 y z w b u))+((d2_3_3 y z w b u)*(d3_0_1 y z w b u)))))))))+((-1)*(d4_3_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_4,d0_1_4,d0_2_3,d0_2_4,d0_3_3,d0_3_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d3_0_1,d3_0_2,d3_0_3,d3_0_4,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d4_3_4]
  ring
#print axioms coefficient_3_4
compact_certificate_declaration theorem coefficient_3_5 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[5]?=some 0 := by
  change some (((((((d0_0_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_3_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_3_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_3_3 y z w b u))+((d2_0_3 y z w b u)*(d3_3_2 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_2_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_2_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_2_3 y z w b u))+((d2_1_3 y z w b u)*(d3_2_2 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_1_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_3 y z w b u))+((d2_2_3 y z w b u)*(d3_1_2 y z w b u)))))+(((d2_3_0 y z w b u)*(d3_0_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_0_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_0_3 y z w b u))+((d2_3_3 y z w b u)*(d3_0_2 y z w b u)))))))))+((-1)*(d4_3_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_5,d0_1_5,d0_2_4,d0_2_5,d0_3_4,d0_3_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d3_0_2,d3_0_3,d3_0_4,d3_0_5,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d4_3_5]
  ring
#print axioms coefficient_3_5

compact_certificate_declaration theorem coefficient_3_6 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[6]?=some 0 := by
  change some (((((((d0_0_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_3_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_3_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_3_4 y z w b u))+((d2_0_3 y z w b u)*(d3_3_3 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_2_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_2_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_2_4 y z w b u))+((d2_1_3 y z w b u)*(d3_2_3 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_1_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_4 y z w b u))+((d2_2_3 y z w b u)*(d3_1_3 y z w b u)))))+(((d2_3_0 y z w b u)*(d3_0_6 y z w b u))+(((d2_3_1 y z w b u)*(d3_0_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_0_4 y z w b u))+((d2_3_3 y z w b u)*(d3_0_3 y z w b u)))))))))+((-1)*(d4_3_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_6,d0_1_6,d0_2_5,d0_2_6,d0_3_5,d0_3_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d3_0_3,d3_0_4,d3_0_5,d3_0_6,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d4_3_6]
  ring
#print axioms coefficient_3_6
compact_certificate_declaration theorem coefficient_3_7 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[7]?=some 0 := by
  change some (((((((d0_0_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_3_7 y z w b u))+(((d2_0_1 y z w b u)*(d3_3_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_3_5 y z w b u))+((d2_0_3 y z w b u)*(d3_3_4 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_2_7 y z w b u))+(((d2_1_1 y z w b u)*(d3_2_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_2_5 y z w b u))+((d2_1_3 y z w b u)*(d3_2_4 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_1_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_5 y z w b u))+((d2_2_3 y z w b u)*(d3_1_4 y z w b u)))))+(((d2_3_1 y z w b u)*(d3_0_6 y z w b u))+(((d2_3_2 y z w b u)*(d3_0_5 y z w b u))+((d2_3_3 y z w b u)*(d3_0_4 y z w b u))))))))+((-1)*(d4_3_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_7,d0_1_7,d0_2_6,d0_2_7,d0_3_6,d0_3_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d3_0_4,d3_0_5,d3_0_6,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d4_3_7]
  ring
#print axioms coefficient_3_7
compact_certificate_declaration theorem coefficient_3_8 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[8]?=some 0 := by
  change some ((((((d0_0_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_1_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_3_8 y z w b u))+(((d2_0_1 y z w b u)*(d3_3_7 y z w b u))+(((d2_0_2 y z w b u)*(d3_3_6 y z w b u))+((d2_0_3 y z w b u)*(d3_3_5 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_2_8 y z w b u))+(((d2_1_1 y z w b u)*(d3_2_7 y z w b u))+(((d2_1_2 y z w b u)*(d3_2_6 y z w b u))+((d2_1_3 y z w b u)*(d3_2_5 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_1_8 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_7 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_6 y z w b u))+((d2_2_3 y z w b u)*(d3_1_5 y z w b u)))))+(((d2_3_2 y z w b u)*(d3_0_6 y z w b u))+((d2_3_3 y z w b u)*(d3_0_5 y z w b u))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_8,d0_1_8,d0_2_7,d0_2_8,d0_3_7,d0_3_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_2,d2_3_3,d3_0_5,d3_0_6,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_3_5,d3_3_6,d3_3_7,d3_3_8]
  ring
#print axioms coefficient_3_8

compact_certificate_declaration theorem coefficient_3_9 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[9]?=some 0 := by
  change some ((((((d0_1_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_9 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_1 y z w b u)*(d3_3_8 y z w b u))+(((d2_0_2 y z w b u)*(d3_3_7 y z w b u))+((d2_0_3 y z w b u)*(d3_3_6 y z w b u))))+((((d2_1_1 y z w b u)*(d3_2_8 y z w b u))+(((d2_1_2 y z w b u)*(d3_2_7 y z w b u))+((d2_1_3 y z w b u)*(d3_2_6 y z w b u))))+((((d2_2_1 y z w b u)*(d3_1_8 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_7 y z w b u))+((d2_2_3 y z w b u)*(d3_1_6 y z w b u))))+((d2_3_3 y z w b u)*(d3_0_6 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_9,d0_2_8,d0_2_9,d0_3_8,d0_3_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_1,d2_0_2,d2_0_3,d2_1_1,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d2_3_3,d3_0_6,d3_1_6,d3_1_7,d3_1_8,d3_2_6,d3_2_7,d3_2_8,d3_3_6,d3_3_7,d3_3_8]
  ring
#print axioms coefficient_3_9
compact_certificate_declaration theorem coefficient_3_10 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[10]?=some 0 := by
  change some ((((((d0_1_10 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_2_9 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_10 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_9 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_10 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_2 y z w b u)*(d3_3_8 y z w b u))+((d2_0_3 y z w b u)*(d3_3_7 y z w b u)))+((((d2_1_2 y z w b u)*(d3_2_8 y z w b u))+((d2_1_3 y z w b u)*(d3_2_7 y z w b u)))+(((d2_2_2 y z w b u)*(d3_1_8 y z w b u))+((d2_2_3 y z w b u)*(d3_1_7 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_10,d0_2_10,d0_2_9,d0_3_10,d0_3_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d2_0_2,d2_0_3,d2_1_2,d2_1_3,d2_2_2,d2_2_3,d3_1_7,d3_1_8,d3_2_7,d3_2_8,d3_3_7,d3_3_8]
  ring
#print axioms coefficient_3_10
compact_certificate_declaration theorem coefficient_3_11 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[11]?=some 0 := by
  change some (((((d0_2_10 y z w b u)*(d1_1_1 y z w b u))+((d0_3_10 y z w b u)*(d1_0_1 y z w b u)))+(((d2_0_3 y z w b u)*(d3_3_8 y z w b u))+(((d2_1_3 y z w b u)*(d3_2_8 y z w b u))+((d2_2_3 y z w b u)*(d3_1_8 y z w b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_10,d0_3_10,d1_0_1,d1_1_1,d2_0_3,d2_1_3,d2_2_3,d3_1_8,d3_2_8,d3_3_8]
  ring
#print axioms coefficient_3_11

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_4 (y z w b u : ℂ) : (innerCertificate4 y z w b u).length=12 := by
  norm_num [innerCertificate4,add,multiply,scale,inner0_1,inner0_2,inner0_3,inner0_4,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner4_4]
compact_certificate_declaration theorem inner_eval_4 (y z w a b u : ℂ) :
    evaluate a (innerCertificate4 y z w b u)=(((((c0_1 y z w a b u)*(c1_3 y z w a b u))+(((c0_2 y z w a b u)*(c1_2 y z w a b u))+(((c0_3 y z w a b u)*(c1_1 y z w a b u))+(((c0_4 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_4 y z w a b u))+(((c2_1 y z w a b u)*(c3_3 y z w a b u))+(((c2_2 y z w a b u)*(c3_2 y z w a b u))+(((c2_3 y z w a b u)*(c3_1 y z w a b u))+(((c2_4 y z w a b u)*(c3_0 y z w a b u))+0))))))+((-1)*(c4_4 y z w a b u))) := by
  simp only [innerCertificate4,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_1,c0_2,c0_3,c0_4,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c3_0,c3_1,c3_2,c3_3,c3_4,c4_4]
#print axioms inner_eval_4

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
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
  change some (((((((d0_1_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_4_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_4_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_4_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_4_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_3_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_3_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_3_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_3_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_2_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_2_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_2_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_1_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_1_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_1_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_1_0 y z w b u))+0))))+(((d2_4_0 y z w b u)*(d3_0_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_0_2 y z w b u))+((d2_4_2 y z w b u)*(d3_0_1 y z w b u)))))))))+((-1)*(d4_4_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_3,d0_2_3,d0_3_2,d0_3_3,d0_4_2,d0_4_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d3_0_1,d3_0_2,d3_0_3,d3_1_0,d3_1_1,d3_1_2,d3_1_3,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d3_4_0,d3_4_1,d3_4_2,d3_4_3,d4_4_3]
  ring
#print axioms coefficient_4_3
compact_certificate_declaration theorem coefficient_4_4 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[4]?=some 0 := by
  change some (((((((d0_1_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_4_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_4_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_4_2 y z w b u))+((d2_0_3 y z w b u)*(d3_4_1 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_3_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_3_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_3_2 y z w b u))+((d2_1_3 y z w b u)*(d3_3_1 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_2_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_2_2 y z w b u))+((d2_2_3 y z w b u)*(d3_2_1 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_1_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_1_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_1_2 y z w b u))+((d2_3_3 y z w b u)*(d3_1_1 y z w b u)))))+(((d2_4_0 y z w b u)*(d3_0_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_0_3 y z w b u))+((d2_4_2 y z w b u)*(d3_0_2 y z w b u)))))))))+((-1)*(d4_4_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_4,d0_2_4,d0_3_3,d0_3_4,d0_4_3,d0_4_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d3_0_2,d3_0_3,d3_0_4,d3_1_1,d3_1_2,d3_1_3,d3_1_4,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d3_4_1,d3_4_2,d3_4_3,d3_4_4,d4_4_4]
  ring
#print axioms coefficient_4_4
compact_certificate_declaration theorem coefficient_4_5 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[5]?=some 0 := by
  change some (((((((d0_1_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_4_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_4_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_4_3 y z w b u))+((d2_0_3 y z w b u)*(d3_4_2 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_3_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_3_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_3_3 y z w b u))+((d2_1_3 y z w b u)*(d3_3_2 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_2_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_2_3 y z w b u))+((d2_2_3 y z w b u)*(d3_2_2 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_1_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_1_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_1_3 y z w b u))+((d2_3_3 y z w b u)*(d3_1_2 y z w b u)))))+(((d2_4_0 y z w b u)*(d3_0_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_0_4 y z w b u))+((d2_4_2 y z w b u)*(d3_0_3 y z w b u)))))))))+((-1)*(d4_4_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_5,d0_2_5,d0_3_4,d0_3_5,d0_4_4,d0_4_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d3_0_3,d3_0_4,d3_0_5,d3_1_2,d3_1_3,d3_1_4,d3_1_5,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d3_4_2,d3_4_3,d3_4_4,d3_4_5,d4_4_5]
  ring
#print axioms coefficient_4_5

compact_certificate_declaration theorem coefficient_4_6 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[6]?=some 0 := by
  change some (((((((d0_1_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_4_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_4_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_4_4 y z w b u))+((d2_0_3 y z w b u)*(d3_4_3 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_3_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_3_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_3_4 y z w b u))+((d2_1_3 y z w b u)*(d3_3_3 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_2_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_2_4 y z w b u))+((d2_2_3 y z w b u)*(d3_2_3 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_1_6 y z w b u))+(((d2_3_1 y z w b u)*(d3_1_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_1_4 y z w b u))+((d2_3_3 y z w b u)*(d3_1_3 y z w b u)))))+(((d2_4_0 y z w b u)*(d3_0_6 y z w b u))+(((d2_4_1 y z w b u)*(d3_0_5 y z w b u))+((d2_4_2 y z w b u)*(d3_0_4 y z w b u)))))))))+((-1)*(d4_4_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_6,d0_2_6,d0_3_5,d0_3_6,d0_4_5,d0_4_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d3_0_4,d3_0_5,d3_0_6,d3_1_3,d3_1_4,d3_1_5,d3_1_6,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d3_4_3,d3_4_4,d3_4_5,d3_4_6,d4_4_6]
  ring
#print axioms coefficient_4_6
compact_certificate_declaration theorem coefficient_4_7 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[7]?=some 0 := by
  change some (((((((d0_1_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_4_7 y z w b u))+(((d2_0_1 y z w b u)*(d3_4_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_4_5 y z w b u))+((d2_0_3 y z w b u)*(d3_4_4 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_3_7 y z w b u))+(((d2_1_1 y z w b u)*(d3_3_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_3_5 y z w b u))+((d2_1_3 y z w b u)*(d3_3_4 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_2_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_2_5 y z w b u))+((d2_2_3 y z w b u)*(d3_2_4 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_1_7 y z w b u))+(((d2_3_1 y z w b u)*(d3_1_6 y z w b u))+(((d2_3_2 y z w b u)*(d3_1_5 y z w b u))+((d2_3_3 y z w b u)*(d3_1_4 y z w b u)))))+(((d2_4_1 y z w b u)*(d3_0_6 y z w b u))+((d2_4_2 y z w b u)*(d3_0_5 y z w b u))))))))+((-1)*(d4_4_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_7,d0_2_7,d0_3_6,d0_3_7,d0_4_6,d0_4_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d3_0_5,d3_0_6,d3_1_4,d3_1_5,d3_1_6,d3_1_7,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d3_4_4,d3_4_5,d3_4_6,d3_4_7,d4_4_7]
  ring
#print axioms coefficient_4_7
compact_certificate_declaration theorem coefficient_4_8 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[8]?=some 0 := by
  change some (((((((d0_1_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_4_8 y z w b u))+(((d2_0_1 y z w b u)*(d3_4_7 y z w b u))+(((d2_0_2 y z w b u)*(d3_4_6 y z w b u))+((d2_0_3 y z w b u)*(d3_4_5 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_3_8 y z w b u))+(((d2_1_1 y z w b u)*(d3_3_7 y z w b u))+(((d2_1_2 y z w b u)*(d3_3_6 y z w b u))+((d2_1_3 y z w b u)*(d3_3_5 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_2_8 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_7 y z w b u))+(((d2_2_2 y z w b u)*(d3_2_6 y z w b u))+((d2_2_3 y z w b u)*(d3_2_5 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_1_8 y z w b u))+(((d2_3_1 y z w b u)*(d3_1_7 y z w b u))+(((d2_3_2 y z w b u)*(d3_1_6 y z w b u))+((d2_3_3 y z w b u)*(d3_1_5 y z w b u)))))+((d2_4_2 y z w b u)*(d3_0_6 y z w b u)))))))+((-1)*(d4_4_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_8,d0_2_8,d0_3_7,d0_3_8,d0_4_7,d0_4_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_2,d3_0_6,d3_1_5,d3_1_6,d3_1_7,d3_1_8,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_3_5,d3_3_6,d3_3_7,d3_3_8,d3_4_5,d3_4_6,d3_4_7,d3_4_8,d4_4_8]
  ring
#print axioms coefficient_4_8

compact_certificate_declaration theorem coefficient_4_9 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[9]?=some 0 := by
  change some ((((((d0_1_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_9 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_4_8 y z w b u))+(((d2_0_2 y z w b u)*(d3_4_7 y z w b u))+((d2_0_3 y z w b u)*(d3_4_6 y z w b u))))+((((d2_1_1 y z w b u)*(d3_3_8 y z w b u))+(((d2_1_2 y z w b u)*(d3_3_7 y z w b u))+((d2_1_3 y z w b u)*(d3_3_6 y z w b u))))+((((d2_2_1 y z w b u)*(d3_2_8 y z w b u))+(((d2_2_2 y z w b u)*(d3_2_7 y z w b u))+((d2_2_3 y z w b u)*(d3_2_6 y z w b u))))+(((d2_3_1 y z w b u)*(d3_1_8 y z w b u))+(((d2_3_2 y z w b u)*(d3_1_7 y z w b u))+((d2_3_3 y z w b u)*(d3_1_6 y z w b u)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_9,d0_2_9,d0_3_8,d0_3_9,d0_4_8,d0_4_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_1_1,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d3_1_6,d3_1_7,d3_1_8,d3_2_6,d3_2_7,d3_2_8,d3_3_6,d3_3_7,d3_3_8,d3_4_6,d3_4_7,d3_4_8]
  ring
#print axioms coefficient_4_9
compact_certificate_declaration theorem coefficient_4_10 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[10]?=some 0 := by
  change some ((((((d0_1_10 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_2_10 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_9 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_10 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_9 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_10 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_4_8 y z w b u))+((d2_0_3 y z w b u)*(d3_4_7 y z w b u)))+((((d2_1_2 y z w b u)*(d3_3_8 y z w b u))+((d2_1_3 y z w b u)*(d3_3_7 y z w b u)))+((((d2_2_2 y z w b u)*(d3_2_8 y z w b u))+((d2_2_3 y z w b u)*(d3_2_7 y z w b u)))+(((d2_3_2 y z w b u)*(d3_1_8 y z w b u))+((d2_3_3 y z w b u)*(d3_1_7 y z w b u))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_10,d0_2_10,d0_3_10,d0_3_9,d0_4_10,d0_4_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_1_2,d2_1_3,d2_2_2,d2_2_3,d2_3_2,d2_3_3,d3_1_7,d3_1_8,d3_2_7,d3_2_8,d3_3_7,d3_3_8,d3_4_7,d3_4_8]
  ring
#print axioms coefficient_4_10
compact_certificate_declaration theorem coefficient_4_11 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[11]?=some 0 := by
  change some (((((d0_3_10 y z w b u)*(d1_1_1 y z w b u))+((d0_4_10 y z w b u)*(d1_0_1 y z w b u)))+(((d2_0_3 y z w b u)*(d3_4_8 y z w b u))+(((d2_1_3 y z w b u)*(d3_3_8 y z w b u))+(((d2_2_3 y z w b u)*(d3_2_8 y z w b u))+((d2_3_3 y z w b u)*(d3_1_8 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_10,d0_4_10,d1_0_1,d1_1_1,d2_0_3,d2_1_3,d2_2_3,d2_3_3,d3_1_8,d3_2_8,d3_3_8,d3_4_8]
  ring
#print axioms coefficient_4_11

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_5 (y z w b u : ℂ) : (innerCertificate5 y z w b u).length=12 := by
  norm_num [innerCertificate5,add,multiply,scale,inner0_2,inner0_3,inner0_4,inner0_5,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner4_5]
compact_certificate_declaration theorem inner_eval_5 (y z w a b u : ℂ) :
    evaluate a (innerCertificate5 y z w b u)=(((((c0_2 y z w a b u)*(c1_3 y z w a b u))+(((c0_3 y z w a b u)*(c1_2 y z w a b u))+(((c0_4 y z w a b u)*(c1_1 y z w a b u))+(((c0_5 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_5 y z w a b u))+(((c2_1 y z w a b u)*(c3_4 y z w a b u))+(((c2_2 y z w a b u)*(c3_3 y z w a b u))+(((c2_3 y z w a b u)*(c3_2 y z w a b u))+(((c2_4 y z w a b u)*(c3_1 y z w a b u))+(((c2_5 y z w a b u)*(c3_0 y z w a b u))+0)))))))+((-1)*(c4_5 y z w a b u))) := by
  simp only [innerCertificate5,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_2,c0_3,c0_4,c0_5,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c3_0,c3_1,c3_2,c3_3,c3_4,c3_5,c4_5]
#print axioms inner_eval_5

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
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
  change some (((((((d0_2_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_5_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_5_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_5_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_4_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_4_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_4_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_3_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_2_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_2_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_2_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_1_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_1_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_1_0 y z w b u))+0)))+(((d2_5_0 y z w b u)*(d3_0_2 y z w b u))+((d2_5_1 y z w b u)*(d3_0_1 y z w b u)))))))))+((-1)*(d4_5_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_2,d0_3_2,d0_4_1,d0_4_2,d0_5_1,d0_5_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d3_0_1,d3_0_2,d3_1_0,d3_1_1,d3_1_2,d3_2_0,d3_2_1,d3_2_2,d3_3_0,d3_3_1,d3_3_2,d3_4_0,d3_4_1,d3_4_2,d3_5_0,d3_5_1,d3_5_2,d4_5_2]
  ring
#print axioms coefficient_5_2

compact_certificate_declaration theorem coefficient_5_3 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[3]?=some 0 := by
  change some (((((((d0_2_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_5_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_5_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_5_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_5_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_4_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_4_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_4_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_4_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_3_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_3_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_2_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_2_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_2_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_2_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_1_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_1_2 y z w b u))+((d2_4_2 y z w b u)*(d3_1_1 y z w b u))))+(((d2_5_0 y z w b u)*(d3_0_3 y z w b u))+((d2_5_1 y z w b u)*(d3_0_2 y z w b u)))))))))+((-1)*(d4_5_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_3,d0_3_3,d0_4_2,d0_4_3,d0_5_2,d0_5_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d3_0_2,d3_0_3,d3_1_1,d3_1_2,d3_1_3,d3_2_0,d3_2_1,d3_2_2,d3_2_3,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d3_4_0,d3_4_1,d3_4_2,d3_4_3,d3_5_0,d3_5_1,d3_5_2,d3_5_3,d4_5_3]
  ring
#print axioms coefficient_5_3
compact_certificate_declaration theorem coefficient_5_4 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[4]?=some 0 := by
  change some (((((((d0_2_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_5_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_5_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_5_2 y z w b u))+((d2_0_3 y z w b u)*(d3_5_1 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_4_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_4_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_4_2 y z w b u))+((d2_1_3 y z w b u)*(d3_4_1 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_3_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_2 y z w b u))+((d2_2_3 y z w b u)*(d3_3_1 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_2_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_2_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_2_2 y z w b u))+((d2_3_3 y z w b u)*(d3_2_1 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_1_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_1_3 y z w b u))+((d2_4_2 y z w b u)*(d3_1_2 y z w b u))))+(((d2_5_0 y z w b u)*(d3_0_4 y z w b u))+((d2_5_1 y z w b u)*(d3_0_3 y z w b u)))))))))+((-1)*(d4_5_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_4,d0_3_4,d0_4_3,d0_4_4,d0_5_3,d0_5_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d3_0_3,d3_0_4,d3_1_2,d3_1_3,d3_1_4,d3_2_1,d3_2_2,d3_2_3,d3_2_4,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d3_4_1,d3_4_2,d3_4_3,d3_4_4,d3_5_1,d3_5_2,d3_5_3,d3_5_4,d4_5_4]
  ring
#print axioms coefficient_5_4
compact_certificate_declaration theorem coefficient_5_5 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[5]?=some 0 := by
  change some (((((((d0_2_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_5_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_5_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_5_3 y z w b u))+((d2_0_3 y z w b u)*(d3_5_2 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_4_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_4_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_4_3 y z w b u))+((d2_1_3 y z w b u)*(d3_4_2 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_3_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_3 y z w b u))+((d2_2_3 y z w b u)*(d3_3_2 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_2_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_2_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_2_3 y z w b u))+((d2_3_3 y z w b u)*(d3_2_2 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_1_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_1_4 y z w b u))+((d2_4_2 y z w b u)*(d3_1_3 y z w b u))))+(((d2_5_0 y z w b u)*(d3_0_5 y z w b u))+((d2_5_1 y z w b u)*(d3_0_4 y z w b u)))))))))+((-1)*(d4_5_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_5,d0_3_5,d0_4_4,d0_4_5,d0_5_4,d0_5_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d3_0_4,d3_0_5,d3_1_3,d3_1_4,d3_1_5,d3_2_2,d3_2_3,d3_2_4,d3_2_5,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d3_4_2,d3_4_3,d3_4_4,d3_4_5,d3_5_2,d3_5_3,d3_5_4,d3_5_5,d4_5_5]
  ring
#print axioms coefficient_5_5

compact_certificate_declaration theorem coefficient_5_6 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[6]?=some 0 := by
  change some (((((((d0_2_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_5_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_5_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_5_4 y z w b u))+((d2_0_3 y z w b u)*(d3_5_3 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_4_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_4_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_4_4 y z w b u))+((d2_1_3 y z w b u)*(d3_4_3 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_3_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_4 y z w b u))+((d2_2_3 y z w b u)*(d3_3_3 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_2_6 y z w b u))+(((d2_3_1 y z w b u)*(d3_2_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_2_4 y z w b u))+((d2_3_3 y z w b u)*(d3_2_3 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_1_6 y z w b u))+(((d2_4_1 y z w b u)*(d3_1_5 y z w b u))+((d2_4_2 y z w b u)*(d3_1_4 y z w b u))))+(((d2_5_0 y z w b u)*(d3_0_6 y z w b u))+((d2_5_1 y z w b u)*(d3_0_5 y z w b u)))))))))+((-1)*(d4_5_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_6,d0_3_6,d0_4_5,d0_4_6,d0_5_5,d0_5_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d3_0_5,d3_0_6,d3_1_4,d3_1_5,d3_1_6,d3_2_3,d3_2_4,d3_2_5,d3_2_6,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d3_4_3,d3_4_4,d3_4_5,d3_4_6,d3_5_3,d3_5_4,d3_5_5,d3_5_6,d4_5_6]
  ring
#print axioms coefficient_5_6
compact_certificate_declaration theorem coefficient_5_7 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[7]?=some 0 := by
  change some (((((((d0_2_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_5_7 y z w b u))+(((d2_0_1 y z w b u)*(d3_5_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_5_5 y z w b u))+((d2_0_3 y z w b u)*(d3_5_4 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_4_7 y z w b u))+(((d2_1_1 y z w b u)*(d3_4_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_4_5 y z w b u))+((d2_1_3 y z w b u)*(d3_4_4 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_3_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_5 y z w b u))+((d2_2_3 y z w b u)*(d3_3_4 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_2_7 y z w b u))+(((d2_3_1 y z w b u)*(d3_2_6 y z w b u))+(((d2_3_2 y z w b u)*(d3_2_5 y z w b u))+((d2_3_3 y z w b u)*(d3_2_4 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_1_7 y z w b u))+(((d2_4_1 y z w b u)*(d3_1_6 y z w b u))+((d2_4_2 y z w b u)*(d3_1_5 y z w b u))))+((d2_5_1 y z w b u)*(d3_0_6 y z w b u))))))))+((-1)*(d4_5_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_7,d0_3_7,d0_4_6,d0_4_7,d0_5_6,d0_5_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_1,d3_0_6,d3_1_5,d3_1_6,d3_1_7,d3_2_4,d3_2_5,d3_2_6,d3_2_7,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d3_4_4,d3_4_5,d3_4_6,d3_4_7,d3_5_4,d3_5_5,d3_5_6,d3_5_7,d4_5_7]
  ring
#print axioms coefficient_5_7
compact_certificate_declaration theorem coefficient_5_8 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[8]?=some 0 := by
  change some (((((((d0_2_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_5_8 y z w b u))+(((d2_0_1 y z w b u)*(d3_5_7 y z w b u))+(((d2_0_2 y z w b u)*(d3_5_6 y z w b u))+((d2_0_3 y z w b u)*(d3_5_5 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_4_8 y z w b u))+(((d2_1_1 y z w b u)*(d3_4_7 y z w b u))+(((d2_1_2 y z w b u)*(d3_4_6 y z w b u))+((d2_1_3 y z w b u)*(d3_4_5 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_3_8 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_7 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_6 y z w b u))+((d2_2_3 y z w b u)*(d3_3_5 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_2_8 y z w b u))+(((d2_3_1 y z w b u)*(d3_2_7 y z w b u))+(((d2_3_2 y z w b u)*(d3_2_6 y z w b u))+((d2_3_3 y z w b u)*(d3_2_5 y z w b u)))))+(((d2_4_0 y z w b u)*(d3_1_8 y z w b u))+(((d2_4_1 y z w b u)*(d3_1_7 y z w b u))+((d2_4_2 y z w b u)*(d3_1_6 y z w b u)))))))))+((-1)*(d4_5_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_8,d0_3_8,d0_4_7,d0_4_8,d0_5_7,d0_5_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d3_1_6,d3_1_7,d3_1_8,d3_2_5,d3_2_6,d3_2_7,d3_2_8,d3_3_5,d3_3_6,d3_3_7,d3_3_8,d3_4_5,d3_4_6,d3_4_7,d3_4_8,d3_5_5,d3_5_6,d3_5_7,d3_5_8,d4_5_8]
  ring
#print axioms coefficient_5_8

compact_certificate_declaration theorem coefficient_5_9 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[9]?=some 0 := by
  change some (((((((d0_2_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_9 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_5_8 y z w b u))+(((d2_0_2 y z w b u)*(d3_5_7 y z w b u))+((d2_0_3 y z w b u)*(d3_5_6 y z w b u))))+((((d2_1_1 y z w b u)*(d3_4_8 y z w b u))+(((d2_1_2 y z w b u)*(d3_4_7 y z w b u))+((d2_1_3 y z w b u)*(d3_4_6 y z w b u))))+((((d2_2_1 y z w b u)*(d3_3_8 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_7 y z w b u))+((d2_2_3 y z w b u)*(d3_3_6 y z w b u))))+((((d2_3_1 y z w b u)*(d3_2_8 y z w b u))+(((d2_3_2 y z w b u)*(d3_2_7 y z w b u))+((d2_3_3 y z w b u)*(d3_2_6 y z w b u))))+(((d2_4_1 y z w b u)*(d3_1_8 y z w b u))+((d2_4_2 y z w b u)*(d3_1_7 y z w b u))))))))+((-1)*(d4_5_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_9,d0_3_9,d0_4_8,d0_4_9,d0_5_8,d0_5_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_1_1,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d3_1_7,d3_1_8,d3_2_6,d3_2_7,d3_2_8,d3_3_6,d3_3_7,d3_3_8,d3_4_6,d3_4_7,d3_4_8,d3_5_6,d3_5_7,d3_5_8,d4_5_9]
  ring
#print axioms coefficient_5_9
compact_certificate_declaration theorem coefficient_5_10 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[10]?=some 0 := by
  change some ((((((d0_2_10 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_10 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_9 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_10 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_9 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_10 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_5_8 y z w b u))+((d2_0_3 y z w b u)*(d3_5_7 y z w b u)))+((((d2_1_2 y z w b u)*(d3_4_8 y z w b u))+((d2_1_3 y z w b u)*(d3_4_7 y z w b u)))+((((d2_2_2 y z w b u)*(d3_3_8 y z w b u))+((d2_2_3 y z w b u)*(d3_3_7 y z w b u)))+((((d2_3_2 y z w b u)*(d3_2_8 y z w b u))+((d2_3_3 y z w b u)*(d3_2_7 y z w b u)))+((d2_4_2 y z w b u)*(d3_1_8 y z w b u))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_10,d0_3_10,d0_4_10,d0_4_9,d0_5_10,d0_5_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_1_2,d2_1_3,d2_2_2,d2_2_3,d2_3_2,d2_3_3,d2_4_2,d3_1_8,d3_2_7,d3_2_8,d3_3_7,d3_3_8,d3_4_7,d3_4_8,d3_5_7,d3_5_8]
  ring
#print axioms coefficient_5_10
compact_certificate_declaration theorem coefficient_5_11 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[11]?=some 0 := by
  change some (((((d0_4_10 y z w b u)*(d1_1_1 y z w b u))+((d0_5_10 y z w b u)*(d1_0_1 y z w b u)))+(((d2_0_3 y z w b u)*(d3_5_8 y z w b u))+(((d2_1_3 y z w b u)*(d3_4_8 y z w b u))+(((d2_2_3 y z w b u)*(d3_3_8 y z w b u))+((d2_3_3 y z w b u)*(d3_2_8 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_10,d0_5_10,d1_0_1,d1_1_1,d2_0_3,d2_1_3,d2_2_3,d2_3_3,d3_2_8,d3_3_8,d3_4_8,d3_5_8]
  ring
#print axioms coefficient_5_11

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_6 (y z w b u : ℂ) : (innerCertificate6 y z w b u).length=12 := by
  norm_num [innerCertificate6,add,multiply,scale,inner0_3,inner0_4,inner0_5,inner0_6,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner4_6]
compact_certificate_declaration theorem inner_eval_6 (y z w a b u : ℂ) :
    evaluate a (innerCertificate6 y z w b u)=(((((c0_3 y z w a b u)*(c1_3 y z w a b u))+(((c0_4 y z w a b u)*(c1_2 y z w a b u))+(((c0_5 y z w a b u)*(c1_1 y z w a b u))+(((c0_6 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_6 y z w a b u))+(((c2_1 y z w a b u)*(c3_5 y z w a b u))+(((c2_2 y z w a b u)*(c3_4 y z w a b u))+(((c2_3 y z w a b u)*(c3_3 y z w a b u))+(((c2_4 y z w a b u)*(c3_2 y z w a b u))+(((c2_5 y z w a b u)*(c3_1 y z w a b u))+(((c2_6 y z w a b u)*(c3_0 y z w a b u))+0))))))))+((-1)*(c4_6 y z w a b u))) := by
  simp only [innerCertificate6,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_3,c0_4,c0_5,c0_6,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c3_0,c3_1,c3_2,c3_3,c3_4,c3_5,c3_6,c4_6]
#print axioms inner_eval_6

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
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
  change some (((((((d0_3_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_6_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_6_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_5_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_5_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_4_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_3_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_2_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_2_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_1_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_1_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_0_1 y z w b u)))))))))+((-1)*(d4_6_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_1,d0_4_1,d0_5_0,d0_5_1,d0_6_0,d0_6_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d3_0_1,d3_1_0,d3_1_1,d3_2_0,d3_2_1,d3_3_0,d3_3_1,d3_4_0,d3_4_1,d3_5_0,d3_5_1,d3_6_0,d3_6_1,d4_6_1]
  ring
#print axioms coefficient_6_1
compact_certificate_declaration theorem coefficient_6_2 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[2]?=some 0 := by
  change some (((((((d0_3_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_6_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_6_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_6_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_5_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_5_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_5_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_4_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_3_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_3_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_2_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_2_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_2_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_1_2 y z w b u))+((d2_5_1 y z w b u)*(d3_1_1 y z w b u)))+((d2_6_0 y z w b u)*(d3_0_2 y z w b u)))))))))+((-1)*(d4_6_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_2,d0_4_2,d0_5_1,d0_5_2,d0_6_1,d0_6_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_0_2,d3_1_1,d3_1_2,d3_2_0,d3_2_1,d3_2_2,d3_3_0,d3_3_1,d3_3_2,d3_4_0,d3_4_1,d3_4_2,d3_5_0,d3_5_1,d3_5_2,d3_6_0,d3_6_1,d3_6_2,d4_6_2]
  ring
#print axioms coefficient_6_2

compact_certificate_declaration theorem coefficient_6_3 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[3]?=some 0 := by
  change some (((((((d0_3_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_6_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_6_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_6_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_6_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_5_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_5_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_5_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_5_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_4_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_4_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_3_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_3_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_3_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_2_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_2_2 y z w b u))+((d2_4_2 y z w b u)*(d3_2_1 y z w b u))))+((((d2_5_0 y z w b u)*(d3_1_3 y z w b u))+((d2_5_1 y z w b u)*(d3_1_2 y z w b u)))+((d2_6_0 y z w b u)*(d3_0_3 y z w b u)))))))))+((-1)*(d4_6_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_3,d0_4_3,d0_5_2,d0_5_3,d0_6_2,d0_6_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_0_3,d3_1_2,d3_1_3,d3_2_1,d3_2_2,d3_2_3,d3_3_0,d3_3_1,d3_3_2,d3_3_3,d3_4_0,d3_4_1,d3_4_2,d3_4_3,d3_5_0,d3_5_1,d3_5_2,d3_5_3,d3_6_0,d3_6_1,d3_6_2,d3_6_3,d4_6_3]
  ring
#print axioms coefficient_6_3
compact_certificate_declaration theorem coefficient_6_4 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[4]?=some 0 := by
  change some (((((((d0_3_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_6_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_6_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_6_2 y z w b u))+((d2_0_3 y z w b u)*(d3_6_1 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_5_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_5_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_5_2 y z w b u))+((d2_1_3 y z w b u)*(d3_5_1 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_4_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_2 y z w b u))+((d2_2_3 y z w b u)*(d3_4_1 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_3_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_3_2 y z w b u))+((d2_3_3 y z w b u)*(d3_3_1 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_2_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_2_3 y z w b u))+((d2_4_2 y z w b u)*(d3_2_2 y z w b u))))+((((d2_5_0 y z w b u)*(d3_1_4 y z w b u))+((d2_5_1 y z w b u)*(d3_1_3 y z w b u)))+((d2_6_0 y z w b u)*(d3_0_4 y z w b u)))))))))+((-1)*(d4_6_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_4,d0_4_4,d0_5_3,d0_5_4,d0_6_3,d0_6_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_0_4,d3_1_3,d3_1_4,d3_2_2,d3_2_3,d3_2_4,d3_3_1,d3_3_2,d3_3_3,d3_3_4,d3_4_1,d3_4_2,d3_4_3,d3_4_4,d3_5_1,d3_5_2,d3_5_3,d3_5_4,d3_6_1,d3_6_2,d3_6_3,d3_6_4,d4_6_4]
  ring
#print axioms coefficient_6_4
compact_certificate_declaration theorem coefficient_6_5 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[5]?=some 0 := by
  change some (((((((d0_3_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_6_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_6_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_6_3 y z w b u))+((d2_0_3 y z w b u)*(d3_6_2 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_5_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_5_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_5_3 y z w b u))+((d2_1_3 y z w b u)*(d3_5_2 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_4_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_3 y z w b u))+((d2_2_3 y z w b u)*(d3_4_2 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_3_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_3_3 y z w b u))+((d2_3_3 y z w b u)*(d3_3_2 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_2_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_2_4 y z w b u))+((d2_4_2 y z w b u)*(d3_2_3 y z w b u))))+((((d2_5_0 y z w b u)*(d3_1_5 y z w b u))+((d2_5_1 y z w b u)*(d3_1_4 y z w b u)))+((d2_6_0 y z w b u)*(d3_0_5 y z w b u)))))))))+((-1)*(d4_6_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_5,d0_4_5,d0_5_4,d0_5_5,d0_6_4,d0_6_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_0_5,d3_1_4,d3_1_5,d3_2_3,d3_2_4,d3_2_5,d3_3_2,d3_3_3,d3_3_4,d3_3_5,d3_4_2,d3_4_3,d3_4_4,d3_4_5,d3_5_2,d3_5_3,d3_5_4,d3_5_5,d3_6_2,d3_6_3,d3_6_4,d3_6_5,d4_6_5]
  ring
#print axioms coefficient_6_5

compact_certificate_declaration theorem coefficient_6_6 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[6]?=some 0 := by
  change some (((((((d0_3_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_6_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_6_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_6_4 y z w b u))+((d2_0_3 y z w b u)*(d3_6_3 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_5_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_5_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_5_4 y z w b u))+((d2_1_3 y z w b u)*(d3_5_3 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_4_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_4 y z w b u))+((d2_2_3 y z w b u)*(d3_4_3 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_3_6 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_3_4 y z w b u))+((d2_3_3 y z w b u)*(d3_3_3 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_2_6 y z w b u))+(((d2_4_1 y z w b u)*(d3_2_5 y z w b u))+((d2_4_2 y z w b u)*(d3_2_4 y z w b u))))+((((d2_5_0 y z w b u)*(d3_1_6 y z w b u))+((d2_5_1 y z w b u)*(d3_1_5 y z w b u)))+((d2_6_0 y z w b u)*(d3_0_6 y z w b u)))))))))+((-1)*(d4_6_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_6,d0_4_6,d0_5_5,d0_5_6,d0_6_5,d0_6_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_0_6,d3_1_5,d3_1_6,d3_2_4,d3_2_5,d3_2_6,d3_3_3,d3_3_4,d3_3_5,d3_3_6,d3_4_3,d3_4_4,d3_4_5,d3_4_6,d3_5_3,d3_5_4,d3_5_5,d3_5_6,d3_6_3,d3_6_4,d3_6_5,d3_6_6,d4_6_6]
  ring
#print axioms coefficient_6_6
compact_certificate_declaration theorem coefficient_6_7 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[7]?=some 0 := by
  change some (((((((d0_3_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_6_7 y z w b u))+(((d2_0_1 y z w b u)*(d3_6_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_6_5 y z w b u))+((d2_0_3 y z w b u)*(d3_6_4 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_5_7 y z w b u))+(((d2_1_1 y z w b u)*(d3_5_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_5_5 y z w b u))+((d2_1_3 y z w b u)*(d3_5_4 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_4_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_5 y z w b u))+((d2_2_3 y z w b u)*(d3_4_4 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_3_7 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_6 y z w b u))+(((d2_3_2 y z w b u)*(d3_3_5 y z w b u))+((d2_3_3 y z w b u)*(d3_3_4 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_2_7 y z w b u))+(((d2_4_1 y z w b u)*(d3_2_6 y z w b u))+((d2_4_2 y z w b u)*(d3_2_5 y z w b u))))+(((d2_5_0 y z w b u)*(d3_1_7 y z w b u))+((d2_5_1 y z w b u)*(d3_1_6 y z w b u)))))))))+((-1)*(d4_6_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_7,d0_4_7,d0_5_6,d0_5_7,d0_6_6,d0_6_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d3_1_6,d3_1_7,d3_2_5,d3_2_6,d3_2_7,d3_3_4,d3_3_5,d3_3_6,d3_3_7,d3_4_4,d3_4_5,d3_4_6,d3_4_7,d3_5_4,d3_5_5,d3_5_6,d3_5_7,d3_6_4,d3_6_5,d3_6_6,d3_6_7,d4_6_7]
  ring
#print axioms coefficient_6_7
compact_certificate_declaration theorem coefficient_6_8 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[8]?=some 0 := by
  change some (((((((d0_3_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_6_8 y z w b u))+(((d2_0_1 y z w b u)*(d3_6_7 y z w b u))+(((d2_0_2 y z w b u)*(d3_6_6 y z w b u))+((d2_0_3 y z w b u)*(d3_6_5 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_5_8 y z w b u))+(((d2_1_1 y z w b u)*(d3_5_7 y z w b u))+(((d2_1_2 y z w b u)*(d3_5_6 y z w b u))+((d2_1_3 y z w b u)*(d3_5_5 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_4_8 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_7 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_6 y z w b u))+((d2_2_3 y z w b u)*(d3_4_5 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_3_8 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_7 y z w b u))+(((d2_3_2 y z w b u)*(d3_3_6 y z w b u))+((d2_3_3 y z w b u)*(d3_3_5 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_2_8 y z w b u))+(((d2_4_1 y z w b u)*(d3_2_7 y z w b u))+((d2_4_2 y z w b u)*(d3_2_6 y z w b u))))+(((d2_5_0 y z w b u)*(d3_1_8 y z w b u))+((d2_5_1 y z w b u)*(d3_1_7 y z w b u)))))))))+((-1)*(d4_6_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_8,d0_4_8,d0_5_7,d0_5_8,d0_6_7,d0_6_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d3_1_7,d3_1_8,d3_2_6,d3_2_7,d3_2_8,d3_3_5,d3_3_6,d3_3_7,d3_3_8,d3_4_5,d3_4_6,d3_4_7,d3_4_8,d3_5_5,d3_5_6,d3_5_7,d3_5_8,d3_6_5,d3_6_6,d3_6_7,d3_6_8,d4_6_8]
  ring
#print axioms coefficient_6_8

compact_certificate_declaration theorem coefficient_6_9 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[9]?=some 0 := by
  change some (((((((d0_3_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_9 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_6_8 y z w b u))+(((d2_0_2 y z w b u)*(d3_6_7 y z w b u))+((d2_0_3 y z w b u)*(d3_6_6 y z w b u))))+((((d2_1_1 y z w b u)*(d3_5_8 y z w b u))+(((d2_1_2 y z w b u)*(d3_5_7 y z w b u))+((d2_1_3 y z w b u)*(d3_5_6 y z w b u))))+((((d2_2_1 y z w b u)*(d3_4_8 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_7 y z w b u))+((d2_2_3 y z w b u)*(d3_4_6 y z w b u))))+((((d2_3_1 y z w b u)*(d3_3_8 y z w b u))+(((d2_3_2 y z w b u)*(d3_3_7 y z w b u))+((d2_3_3 y z w b u)*(d3_3_6 y z w b u))))+((((d2_4_1 y z w b u)*(d3_2_8 y z w b u))+((d2_4_2 y z w b u)*(d3_2_7 y z w b u)))+((d2_5_1 y z w b u)*(d3_1_8 y z w b u))))))))+((-1)*(d4_6_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_9,d0_4_9,d0_5_8,d0_5_9,d0_6_8,d0_6_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_1_1,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d2_5_1,d3_1_8,d3_2_7,d3_2_8,d3_3_6,d3_3_7,d3_3_8,d3_4_6,d3_4_7,d3_4_8,d3_5_6,d3_5_7,d3_5_8,d3_6_6,d3_6_7,d3_6_8,d4_6_9]
  ring
#print axioms coefficient_6_9
compact_certificate_declaration theorem coefficient_6_10 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[10]?=some 0 := by
  change some ((((((d0_3_10 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_10 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_9 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_10 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_9 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_10 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_6_8 y z w b u))+((d2_0_3 y z w b u)*(d3_6_7 y z w b u)))+((((d2_1_2 y z w b u)*(d3_5_8 y z w b u))+((d2_1_3 y z w b u)*(d3_5_7 y z w b u)))+((((d2_2_2 y z w b u)*(d3_4_8 y z w b u))+((d2_2_3 y z w b u)*(d3_4_7 y z w b u)))+((((d2_3_2 y z w b u)*(d3_3_8 y z w b u))+((d2_3_3 y z w b u)*(d3_3_7 y z w b u)))+((d2_4_2 y z w b u)*(d3_2_8 y z w b u))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_10,d0_4_10,d0_5_10,d0_5_9,d0_6_10,d0_6_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_1_2,d2_1_3,d2_2_2,d2_2_3,d2_3_2,d2_3_3,d2_4_2,d3_2_8,d3_3_7,d3_3_8,d3_4_7,d3_4_8,d3_5_7,d3_5_8,d3_6_7,d3_6_8]
  ring
#print axioms coefficient_6_10
compact_certificate_declaration theorem coefficient_6_11 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[11]?=some 0 := by
  change some (((((d0_5_10 y z w b u)*(d1_1_1 y z w b u))+((d0_6_10 y z w b u)*(d1_0_1 y z w b u)))+(((d2_0_3 y z w b u)*(d3_6_8 y z w b u))+(((d2_1_3 y z w b u)*(d3_5_8 y z w b u))+(((d2_2_3 y z w b u)*(d3_4_8 y z w b u))+((d2_3_3 y z w b u)*(d3_3_8 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_5_10,d0_6_10,d1_0_1,d1_1_1,d2_0_3,d2_1_3,d2_2_3,d2_3_3,d3_3_8,d3_4_8,d3_5_8,d3_6_8]
  ring
#print axioms coefficient_6_11

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_7 (y z w b u : ℂ) : (innerCertificate7 y z w b u).length=12 := by
  norm_num [innerCertificate7,add,multiply,scale,inner0_4,inner0_5,inner0_6,inner0_7,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner4_7]
compact_certificate_declaration theorem inner_eval_7 (y z w a b u : ℂ) :
    evaluate a (innerCertificate7 y z w b u)=(((((c0_4 y z w a b u)*(c1_3 y z w a b u))+(((c0_5 y z w a b u)*(c1_2 y z w a b u))+(((c0_6 y z w a b u)*(c1_1 y z w a b u))+(((c0_7 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_7 y z w a b u))+(((c2_1 y z w a b u)*(c3_6 y z w a b u))+(((c2_2 y z w a b u)*(c3_5 y z w a b u))+(((c2_3 y z w a b u)*(c3_4 y z w a b u))+(((c2_4 y z w a b u)*(c3_3 y z w a b u))+(((c2_5 y z w a b u)*(c3_2 y z w a b u))+((c2_6 y z w a b u)*(c3_1 y z w a b u)))))))))+((-1)*(c4_7 y z w a b u))) := by
  simp only [innerCertificate7,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_4,c0_5,c0_6,c0_7,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c3_1,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c4_7]
#print axioms inner_eval_7

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_7_0 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[0]?=some 0 := by
  change some (((((((d0_4_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_7_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_7_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_6_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_5_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_4_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_3_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_2_0 y z w b u))+0)+(((d2_6_0 y z w b u)*(d3_1_0 y z w b u))+0))))))))+(((-1)*(d4_7_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_0,d0_5_0,d0_6_0,d0_7_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d4_7_0]
  ring
#print axioms coefficient_7_0
compact_certificate_declaration theorem coefficient_7_1 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[1]?=some 0 := by
  change some (((((((d0_4_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_7_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_7_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_6_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_6_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_5_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_4_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_3_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_3_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_2_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_2_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_1_1 y z w b u)))))))))+((-1)*(d4_7_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_1,d0_5_1,d0_6_0,d0_6_1,d0_7_0,d0_7_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d3_1_1,d3_2_0,d3_2_1,d3_3_0,d3_3_1,d3_4_0,d3_4_1,d3_5_0,d3_5_1,d3_6_0,d3_6_1,d3_7_0,d3_7_1,d4_7_1]
  ring
#print axioms coefficient_7_1
compact_certificate_declaration theorem coefficient_7_2 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[2]?=some 0 := by
  change some (((((((d0_4_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_7_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_7_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_7_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_6_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_6_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_6_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_5_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_4_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_4_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_3_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_3_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_3_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_2_2 y z w b u))+((d2_5_1 y z w b u)*(d3_2_1 y z w b u)))+((d2_6_0 y z w b u)*(d3_1_2 y z w b u)))))))))+((-1)*(d4_7_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_2,d0_5_2,d0_6_1,d0_6_2,d0_7_1,d0_7_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_1_2,d3_2_1,d3_2_2,d3_3_0,d3_3_1,d3_3_2,d3_4_0,d3_4_1,d3_4_2,d3_5_0,d3_5_1,d3_5_2,d3_6_0,d3_6_1,d3_6_2,d3_7_0,d3_7_1,d3_7_2,d4_7_2]
  ring
#print axioms coefficient_7_2

compact_certificate_declaration theorem coefficient_7_3 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[3]?=some 0 := by
  change some (((((((d0_4_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_7_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_7_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_7_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_7_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_6_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_6_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_6_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_6_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_5_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_5_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_4_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_4_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_4_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_3_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_3_2 y z w b u))+((d2_4_2 y z w b u)*(d3_3_1 y z w b u))))+((((d2_5_0 y z w b u)*(d3_2_3 y z w b u))+((d2_5_1 y z w b u)*(d3_2_2 y z w b u)))+((d2_6_0 y z w b u)*(d3_1_3 y z w b u)))))))))+((-1)*(d4_7_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_3,d0_5_3,d0_6_2,d0_6_3,d0_7_2,d0_7_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_1_3,d3_2_2,d3_2_3,d3_3_1,d3_3_2,d3_3_3,d3_4_0,d3_4_1,d3_4_2,d3_4_3,d3_5_0,d3_5_1,d3_5_2,d3_5_3,d3_6_0,d3_6_1,d3_6_2,d3_6_3,d3_7_0,d3_7_1,d3_7_2,d3_7_3,d4_7_3]
  ring
#print axioms coefficient_7_3
compact_certificate_declaration theorem coefficient_7_4 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[4]?=some 0 := by
  change some (((((((d0_4_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_7_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_7_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_7_2 y z w b u))+((d2_0_3 y z w b u)*(d3_7_1 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_6_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_6_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_6_2 y z w b u))+((d2_1_3 y z w b u)*(d3_6_1 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_5_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_2 y z w b u))+((d2_2_3 y z w b u)*(d3_5_1 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_4_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_4_2 y z w b u))+((d2_3_3 y z w b u)*(d3_4_1 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_3_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_3_3 y z w b u))+((d2_4_2 y z w b u)*(d3_3_2 y z w b u))))+((((d2_5_0 y z w b u)*(d3_2_4 y z w b u))+((d2_5_1 y z w b u)*(d3_2_3 y z w b u)))+((d2_6_0 y z w b u)*(d3_1_4 y z w b u)))))))))+((-1)*(d4_7_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_4,d0_5_4,d0_6_3,d0_6_4,d0_7_3,d0_7_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_1_4,d3_2_3,d3_2_4,d3_3_2,d3_3_3,d3_3_4,d3_4_1,d3_4_2,d3_4_3,d3_4_4,d3_5_1,d3_5_2,d3_5_3,d3_5_4,d3_6_1,d3_6_2,d3_6_3,d3_6_4,d3_7_1,d3_7_2,d3_7_3,d3_7_4,d4_7_4]
  ring
#print axioms coefficient_7_4
compact_certificate_declaration theorem coefficient_7_5 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[5]?=some 0 := by
  change some (((((((d0_4_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_7_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_7_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_7_3 y z w b u))+((d2_0_3 y z w b u)*(d3_7_2 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_6_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_6_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_6_3 y z w b u))+((d2_1_3 y z w b u)*(d3_6_2 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_5_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_3 y z w b u))+((d2_2_3 y z w b u)*(d3_5_2 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_4_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_4_3 y z w b u))+((d2_3_3 y z w b u)*(d3_4_2 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_3_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_3_4 y z w b u))+((d2_4_2 y z w b u)*(d3_3_3 y z w b u))))+((((d2_5_0 y z w b u)*(d3_2_5 y z w b u))+((d2_5_1 y z w b u)*(d3_2_4 y z w b u)))+((d2_6_0 y z w b u)*(d3_1_5 y z w b u)))))))))+((-1)*(d4_7_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_5,d0_5_5,d0_6_4,d0_6_5,d0_7_4,d0_7_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_1_5,d3_2_4,d3_2_5,d3_3_3,d3_3_4,d3_3_5,d3_4_2,d3_4_3,d3_4_4,d3_4_5,d3_5_2,d3_5_3,d3_5_4,d3_5_5,d3_6_2,d3_6_3,d3_6_4,d3_6_5,d3_7_2,d3_7_3,d3_7_4,d3_7_5,d4_7_5]
  ring
#print axioms coefficient_7_5

compact_certificate_declaration theorem coefficient_7_6 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[6]?=some 0 := by
  change some (((((((d0_4_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_7_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_7_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_7_4 y z w b u))+((d2_0_3 y z w b u)*(d3_7_3 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_6_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_6_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_6_4 y z w b u))+((d2_1_3 y z w b u)*(d3_6_3 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_5_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_4 y z w b u))+((d2_2_3 y z w b u)*(d3_5_3 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_4_6 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_4_4 y z w b u))+((d2_3_3 y z w b u)*(d3_4_3 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_3_6 y z w b u))+(((d2_4_1 y z w b u)*(d3_3_5 y z w b u))+((d2_4_2 y z w b u)*(d3_3_4 y z w b u))))+((((d2_5_0 y z w b u)*(d3_2_6 y z w b u))+((d2_5_1 y z w b u)*(d3_2_5 y z w b u)))+((d2_6_0 y z w b u)*(d3_1_6 y z w b u)))))))))+((-1)*(d4_7_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_6,d0_5_6,d0_6_5,d0_6_6,d0_7_5,d0_7_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_1_6,d3_2_5,d3_2_6,d3_3_4,d3_3_5,d3_3_6,d3_4_3,d3_4_4,d3_4_5,d3_4_6,d3_5_3,d3_5_4,d3_5_5,d3_5_6,d3_6_3,d3_6_4,d3_6_5,d3_6_6,d3_7_3,d3_7_4,d3_7_5,d3_7_6,d4_7_6]
  ring
#print axioms coefficient_7_6
compact_certificate_declaration theorem coefficient_7_7 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[7]?=some 0 := by
  change some (((((((d0_4_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_7_7 y z w b u))+(((d2_0_1 y z w b u)*(d3_7_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_7_5 y z w b u))+((d2_0_3 y z w b u)*(d3_7_4 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_6_7 y z w b u))+(((d2_1_1 y z w b u)*(d3_6_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_6_5 y z w b u))+((d2_1_3 y z w b u)*(d3_6_4 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_5_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_5 y z w b u))+((d2_2_3 y z w b u)*(d3_5_4 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_4_7 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_6 y z w b u))+(((d2_3_2 y z w b u)*(d3_4_5 y z w b u))+((d2_3_3 y z w b u)*(d3_4_4 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_3_7 y z w b u))+(((d2_4_1 y z w b u)*(d3_3_6 y z w b u))+((d2_4_2 y z w b u)*(d3_3_5 y z w b u))))+((((d2_5_0 y z w b u)*(d3_2_7 y z w b u))+((d2_5_1 y z w b u)*(d3_2_6 y z w b u)))+((d2_6_0 y z w b u)*(d3_1_7 y z w b u)))))))))+((-1)*(d4_7_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_7,d0_5_7,d0_6_6,d0_6_7,d0_7_6,d0_7_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_1_7,d3_2_6,d3_2_7,d3_3_5,d3_3_6,d3_3_7,d3_4_4,d3_4_5,d3_4_6,d3_4_7,d3_5_4,d3_5_5,d3_5_6,d3_5_7,d3_6_4,d3_6_5,d3_6_6,d3_6_7,d3_7_4,d3_7_5,d3_7_6,d3_7_7,d4_7_7]
  ring
#print axioms coefficient_7_7
compact_certificate_declaration theorem coefficient_7_8 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[8]?=some 0 := by
  change some (((((((d0_4_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_7_7 y z w b u))+(((d2_0_2 y z w b u)*(d3_7_6 y z w b u))+((d2_0_3 y z w b u)*(d3_7_5 y z w b u))))+((((d2_1_0 y z w b u)*(d3_6_8 y z w b u))+(((d2_1_1 y z w b u)*(d3_6_7 y z w b u))+(((d2_1_2 y z w b u)*(d3_6_6 y z w b u))+((d2_1_3 y z w b u)*(d3_6_5 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_5_8 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_7 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_6 y z w b u))+((d2_2_3 y z w b u)*(d3_5_5 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_4_8 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_7 y z w b u))+(((d2_3_2 y z w b u)*(d3_4_6 y z w b u))+((d2_3_3 y z w b u)*(d3_4_5 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_3_8 y z w b u))+(((d2_4_1 y z w b u)*(d3_3_7 y z w b u))+((d2_4_2 y z w b u)*(d3_3_6 y z w b u))))+((((d2_5_0 y z w b u)*(d3_2_8 y z w b u))+((d2_5_1 y z w b u)*(d3_2_7 y z w b u)))+((d2_6_0 y z w b u)*(d3_1_8 y z w b u)))))))))+((-1)*(d4_7_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_8,d0_5_8,d0_6_7,d0_6_8,d0_7_7,d0_7_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_1_8,d3_2_7,d3_2_8,d3_3_6,d3_3_7,d3_3_8,d3_4_5,d3_4_6,d3_4_7,d3_4_8,d3_5_5,d3_5_6,d3_5_7,d3_5_8,d3_6_5,d3_6_6,d3_6_7,d3_6_8,d3_7_5,d3_7_6,d3_7_7,d4_7_8]
  ring
#print axioms coefficient_7_8

compact_certificate_declaration theorem coefficient_7_9 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[9]?=some 0 := by
  change some (((((((d0_4_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_9 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_7_7 y z w b u))+((d2_0_3 y z w b u)*(d3_7_6 y z w b u)))+((((d2_1_1 y z w b u)*(d3_6_8 y z w b u))+(((d2_1_2 y z w b u)*(d3_6_7 y z w b u))+((d2_1_3 y z w b u)*(d3_6_6 y z w b u))))+((((d2_2_1 y z w b u)*(d3_5_8 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_7 y z w b u))+((d2_2_3 y z w b u)*(d3_5_6 y z w b u))))+((((d2_3_1 y z w b u)*(d3_4_8 y z w b u))+(((d2_3_2 y z w b u)*(d3_4_7 y z w b u))+((d2_3_3 y z w b u)*(d3_4_6 y z w b u))))+((((d2_4_1 y z w b u)*(d3_3_8 y z w b u))+((d2_4_2 y z w b u)*(d3_3_7 y z w b u)))+((d2_5_1 y z w b u)*(d3_2_8 y z w b u))))))))+((-1)*(d4_7_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_9,d0_5_9,d0_6_8,d0_6_9,d0_7_8,d0_7_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_1_1,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d2_5_1,d3_2_8,d3_3_7,d3_3_8,d3_4_6,d3_4_7,d3_4_8,d3_5_6,d3_5_7,d3_5_8,d3_6_6,d3_6_7,d3_6_8,d3_7_6,d3_7_7,d4_7_9]
  ring
#print axioms coefficient_7_9
compact_certificate_declaration theorem coefficient_7_10 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[10]?=some 0 := by
  change some ((((((d0_4_10 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_10 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_9 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_10 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_9 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_10 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_0_3 y z w b u)*(d3_7_7 y z w b u))+((((d2_1_2 y z w b u)*(d3_6_8 y z w b u))+((d2_1_3 y z w b u)*(d3_6_7 y z w b u)))+((((d2_2_2 y z w b u)*(d3_5_8 y z w b u))+((d2_2_3 y z w b u)*(d3_5_7 y z w b u)))+((((d2_3_2 y z w b u)*(d3_4_8 y z w b u))+((d2_3_3 y z w b u)*(d3_4_7 y z w b u)))+((d2_4_2 y z w b u)*(d3_3_8 y z w b u))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_10,d0_5_10,d0_6_10,d0_6_9,d0_7_10,d0_7_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_1_2,d2_1_3,d2_2_2,d2_2_3,d2_3_2,d2_3_3,d2_4_2,d3_3_8,d3_4_7,d3_4_8,d3_5_7,d3_5_8,d3_6_7,d3_6_8,d3_7_7]
  ring
#print axioms coefficient_7_10
compact_certificate_declaration theorem coefficient_7_11 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[11]?=some 0 := by
  change some (((((d0_6_10 y z w b u)*(d1_1_1 y z w b u))+((d0_7_10 y z w b u)*(d1_0_1 y z w b u)))+(((d2_1_3 y z w b u)*(d3_6_8 y z w b u))+(((d2_2_3 y z w b u)*(d3_5_8 y z w b u))+((d2_3_3 y z w b u)*(d3_4_8 y z w b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_6_10,d0_7_10,d1_0_1,d1_1_1,d2_1_3,d2_2_3,d2_3_3,d3_4_8,d3_5_8,d3_6_8]
  ring
#print axioms coefficient_7_11

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_8 (y z w b u : ℂ) : (innerCertificate8 y z w b u).length=12 := by
  norm_num [innerCertificate8,add,multiply,scale,inner0_5,inner0_6,inner0_7,inner0_8,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner4_8]
compact_certificate_declaration theorem inner_eval_8 (y z w a b u : ℂ) :
    evaluate a (innerCertificate8 y z w b u)=(((((c0_5 y z w a b u)*(c1_3 y z w a b u))+(((c0_6 y z w a b u)*(c1_2 y z w a b u))+(((c0_7 y z w a b u)*(c1_1 y z w a b u))+(((c0_8 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_8 y z w a b u))+(((c2_1 y z w a b u)*(c3_7 y z w a b u))+(((c2_2 y z w a b u)*(c3_6 y z w a b u))+(((c2_3 y z w a b u)*(c3_5 y z w a b u))+(((c2_4 y z w a b u)*(c3_4 y z w a b u))+(((c2_5 y z w a b u)*(c3_3 y z w a b u))+((c2_6 y z w a b u)*(c3_2 y z w a b u)))))))))+((-1)*(c4_8 y z w a b u))) := by
  simp only [innerCertificate8,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_5,c0_6,c0_7,c0_8,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c4_8]
#print axioms inner_eval_8

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_8_0 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[0]?=some 0 := by
  change some (((((((d0_5_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_6_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_7_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_8_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_8_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_7_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_6_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_5_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_4_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_3_0 y z w b u))+0)+(((d2_6_0 y z w b u)*(d3_2_0 y z w b u))+0))))))))+(((-1)*(d4_8_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_5_0,d0_6_0,d0_7_0,d0_8_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_8_0]
  ring
#print axioms coefficient_8_0
compact_certificate_declaration theorem coefficient_8_1 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[1]?=some 0 := by
  change some (((((((d0_5_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_6_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_7_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_7_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_8_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_8_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_8_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_8_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_7_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_7_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_6_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_6_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_5_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_5_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_4_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_4_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_3_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_3_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_2_1 y z w b u)))))))))+((-1)*(d4_8_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_5_1,d0_6_1,d0_7_0,d0_7_1,d0_8_0,d0_8_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d3_2_1,d3_3_0,d3_3_1,d3_4_0,d3_4_1,d3_5_0,d3_5_1,d3_6_0,d3_6_1,d3_7_0,d3_7_1,d3_8_0,d3_8_1,d4_8_1]
  ring
#print axioms coefficient_8_1
compact_certificate_declaration theorem coefficient_8_2 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[2]?=some 0 := by
  change some (((((((d0_5_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_6_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_7_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_7_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_8_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_8_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_8_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_8_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_8_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_7_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_7_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_7_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_6_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_6_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_6_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_5_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_5_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_5_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_4_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_4_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_4_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_3_2 y z w b u))+((d2_5_1 y z w b u)*(d3_3_1 y z w b u)))+((d2_6_0 y z w b u)*(d3_2_2 y z w b u)))))))))+((-1)*(d4_8_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_5_2,d0_6_2,d0_7_1,d0_7_2,d0_8_1,d0_8_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_2_2,d3_3_1,d3_3_2,d3_4_0,d3_4_1,d3_4_2,d3_5_0,d3_5_1,d3_5_2,d3_6_0,d3_6_1,d3_6_2,d3_7_0,d3_7_1,d3_7_2,d3_8_0,d3_8_1,d3_8_2,d4_8_2]
  ring
#print axioms coefficient_8_2

compact_certificate_declaration theorem coefficient_8_3 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[3]?=some 0 := by
  change some (((((((d0_5_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_6_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_7_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_7_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_8_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_8_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_8_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_8_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_8_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_8_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_7_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_7_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_7_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_7_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_6_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_6_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_6_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_6_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_5_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_5_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_5_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_5_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_4_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_4_2 y z w b u))+((d2_4_2 y z w b u)*(d3_4_1 y z w b u))))+((((d2_5_0 y z w b u)*(d3_3_3 y z w b u))+((d2_5_1 y z w b u)*(d3_3_2 y z w b u)))+((d2_6_0 y z w b u)*(d3_2_3 y z w b u)))))))))+((-1)*(d4_8_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_5_3,d0_6_3,d0_7_2,d0_7_3,d0_8_2,d0_8_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_2_3,d3_3_2,d3_3_3,d3_4_1,d3_4_2,d3_4_3,d3_5_0,d3_5_1,d3_5_2,d3_5_3,d3_6_0,d3_6_1,d3_6_2,d3_6_3,d3_7_0,d3_7_1,d3_7_2,d3_7_3,d3_8_0,d3_8_1,d3_8_2,d3_8_3,d4_8_3]
  ring
#print axioms coefficient_8_3
compact_certificate_declaration theorem coefficient_8_4 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[4]?=some 0 := by
  change some (((((((d0_5_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_6_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_7_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_7_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_8_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_8_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_8_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_8_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_8_2 y z w b u))+((d2_0_3 y z w b u)*(d3_8_1 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_7_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_7_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_7_2 y z w b u))+((d2_1_3 y z w b u)*(d3_7_1 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_6_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_6_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_6_2 y z w b u))+((d2_2_3 y z w b u)*(d3_6_1 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_5_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_5_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_5_2 y z w b u))+((d2_3_3 y z w b u)*(d3_5_1 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_4_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_4_3 y z w b u))+((d2_4_2 y z w b u)*(d3_4_2 y z w b u))))+((((d2_5_0 y z w b u)*(d3_3_4 y z w b u))+((d2_5_1 y z w b u)*(d3_3_3 y z w b u)))+((d2_6_0 y z w b u)*(d3_2_4 y z w b u)))))))))+((-1)*(d4_8_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_5_4,d0_6_4,d0_7_3,d0_7_4,d0_8_3,d0_8_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_2_4,d3_3_3,d3_3_4,d3_4_2,d3_4_3,d3_4_4,d3_5_1,d3_5_2,d3_5_3,d3_5_4,d3_6_1,d3_6_2,d3_6_3,d3_6_4,d3_7_1,d3_7_2,d3_7_3,d3_7_4,d3_8_1,d3_8_2,d3_8_3,d3_8_4,d4_8_4]
  ring
#print axioms coefficient_8_4
compact_certificate_declaration theorem coefficient_8_5 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[5]?=some 0 := by
  change some (((((((d0_5_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_6_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_7_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_7_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_8_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_8_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_8_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_8_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_8_3 y z w b u))+((d2_0_3 y z w b u)*(d3_8_2 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_7_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_7_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_7_3 y z w b u))+((d2_1_3 y z w b u)*(d3_7_2 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_6_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_6_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_6_3 y z w b u))+((d2_2_3 y z w b u)*(d3_6_2 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_5_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_5_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_5_3 y z w b u))+((d2_3_3 y z w b u)*(d3_5_2 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_4_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_4_4 y z w b u))+((d2_4_2 y z w b u)*(d3_4_3 y z w b u))))+((((d2_5_0 y z w b u)*(d3_3_5 y z w b u))+((d2_5_1 y z w b u)*(d3_3_4 y z w b u)))+((d2_6_0 y z w b u)*(d3_2_5 y z w b u)))))))))+((-1)*(d4_8_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_5_5,d0_6_5,d0_7_4,d0_7_5,d0_8_4,d0_8_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_2_5,d3_3_4,d3_3_5,d3_4_3,d3_4_4,d3_4_5,d3_5_2,d3_5_3,d3_5_4,d3_5_5,d3_6_2,d3_6_3,d3_6_4,d3_6_5,d3_7_2,d3_7_3,d3_7_4,d3_7_5,d3_8_2,d3_8_3,d3_8_4,d3_8_5,d4_8_5]
  ring
#print axioms coefficient_8_5

compact_certificate_declaration theorem coefficient_8_6 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[6]?=some 0 := by
  change some (((((((d0_5_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_6_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_7_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_7_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_8_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_8_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_8_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_8_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_8_4 y z w b u))+((d2_0_3 y z w b u)*(d3_8_3 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_7_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_7_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_7_4 y z w b u))+((d2_1_3 y z w b u)*(d3_7_3 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_6_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_6_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_6_4 y z w b u))+((d2_2_3 y z w b u)*(d3_6_3 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_5_6 y z w b u))+(((d2_3_1 y z w b u)*(d3_5_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_5_4 y z w b u))+((d2_3_3 y z w b u)*(d3_5_3 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_4_6 y z w b u))+(((d2_4_1 y z w b u)*(d3_4_5 y z w b u))+((d2_4_2 y z w b u)*(d3_4_4 y z w b u))))+((((d2_5_0 y z w b u)*(d3_3_6 y z w b u))+((d2_5_1 y z w b u)*(d3_3_5 y z w b u)))+((d2_6_0 y z w b u)*(d3_2_6 y z w b u)))))))))+((-1)*(d4_8_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_5_6,d0_6_6,d0_7_5,d0_7_6,d0_8_5,d0_8_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_2_6,d3_3_5,d3_3_6,d3_4_4,d3_4_5,d3_4_6,d3_5_3,d3_5_4,d3_5_5,d3_5_6,d3_6_3,d3_6_4,d3_6_5,d3_6_6,d3_7_3,d3_7_4,d3_7_5,d3_7_6,d3_8_3,d3_8_4,d3_8_5,d3_8_6,d4_8_6]
  ring
#print axioms coefficient_8_6
compact_certificate_declaration theorem coefficient_8_7 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[7]?=some 0 := by
  change some (((((((d0_5_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_6_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_7_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_7_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_8_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_8_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_8_7 y z w b u))+(((d2_0_1 y z w b u)*(d3_8_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_8_5 y z w b u))+((d2_0_3 y z w b u)*(d3_8_4 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_7_7 y z w b u))+(((d2_1_1 y z w b u)*(d3_7_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_7_5 y z w b u))+((d2_1_3 y z w b u)*(d3_7_4 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_6_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_6_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_6_5 y z w b u))+((d2_2_3 y z w b u)*(d3_6_4 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_5_7 y z w b u))+(((d2_3_1 y z w b u)*(d3_5_6 y z w b u))+(((d2_3_2 y z w b u)*(d3_5_5 y z w b u))+((d2_3_3 y z w b u)*(d3_5_4 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_4_7 y z w b u))+(((d2_4_1 y z w b u)*(d3_4_6 y z w b u))+((d2_4_2 y z w b u)*(d3_4_5 y z w b u))))+((((d2_5_0 y z w b u)*(d3_3_7 y z w b u))+((d2_5_1 y z w b u)*(d3_3_6 y z w b u)))+((d2_6_0 y z w b u)*(d3_2_7 y z w b u)))))))))+((-1)*(d4_8_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_5_7,d0_6_7,d0_7_6,d0_7_7,d0_8_6,d0_8_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_2_7,d3_3_6,d3_3_7,d3_4_5,d3_4_6,d3_4_7,d3_5_4,d3_5_5,d3_5_6,d3_5_7,d3_6_4,d3_6_5,d3_6_6,d3_6_7,d3_7_4,d3_7_5,d3_7_6,d3_7_7,d3_8_4,d3_8_5,d3_8_6,d3_8_7,d4_8_7]
  ring
#print axioms coefficient_8_7
compact_certificate_declaration theorem coefficient_8_8 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[8]?=some 0 := by
  change some (((((((d0_5_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_6_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_7_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_7_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_8_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_8_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_8_7 y z w b u))+(((d2_0_2 y z w b u)*(d3_8_6 y z w b u))+((d2_0_3 y z w b u)*(d3_8_5 y z w b u))))+((((d2_1_1 y z w b u)*(d3_7_7 y z w b u))+(((d2_1_2 y z w b u)*(d3_7_6 y z w b u))+((d2_1_3 y z w b u)*(d3_7_5 y z w b u))))+((((d2_2_0 y z w b u)*(d3_6_8 y z w b u))+(((d2_2_1 y z w b u)*(d3_6_7 y z w b u))+(((d2_2_2 y z w b u)*(d3_6_6 y z w b u))+((d2_2_3 y z w b u)*(d3_6_5 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_5_8 y z w b u))+(((d2_3_1 y z w b u)*(d3_5_7 y z w b u))+(((d2_3_2 y z w b u)*(d3_5_6 y z w b u))+((d2_3_3 y z w b u)*(d3_5_5 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_4_8 y z w b u))+(((d2_4_1 y z w b u)*(d3_4_7 y z w b u))+((d2_4_2 y z w b u)*(d3_4_6 y z w b u))))+((((d2_5_0 y z w b u)*(d3_3_8 y z w b u))+((d2_5_1 y z w b u)*(d3_3_7 y z w b u)))+((d2_6_0 y z w b u)*(d3_2_8 y z w b u)))))))))+((-1)*(d4_8_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_5_8,d0_6_8,d0_7_7,d0_7_8,d0_8_7,d0_8_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_2_8,d3_3_7,d3_3_8,d3_4_6,d3_4_7,d3_4_8,d3_5_5,d3_5_6,d3_5_7,d3_5_8,d3_6_5,d3_6_6,d3_6_7,d3_6_8,d3_7_5,d3_7_6,d3_7_7,d3_8_5,d3_8_6,d3_8_7,d4_8_8]
  ring
#print axioms coefficient_8_8

compact_certificate_declaration theorem coefficient_8_9 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[9]?=some 0 := by
  change some (((((((d0_5_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_6_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_7_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_7_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_8_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_8_9 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_8_7 y z w b u))+((d2_0_3 y z w b u)*(d3_8_6 y z w b u)))+((((d2_1_2 y z w b u)*(d3_7_7 y z w b u))+((d2_1_3 y z w b u)*(d3_7_6 y z w b u)))+((((d2_2_1 y z w b u)*(d3_6_8 y z w b u))+(((d2_2_2 y z w b u)*(d3_6_7 y z w b u))+((d2_2_3 y z w b u)*(d3_6_6 y z w b u))))+((((d2_3_1 y z w b u)*(d3_5_8 y z w b u))+(((d2_3_2 y z w b u)*(d3_5_7 y z w b u))+((d2_3_3 y z w b u)*(d3_5_6 y z w b u))))+((((d2_4_1 y z w b u)*(d3_4_8 y z w b u))+((d2_4_2 y z w b u)*(d3_4_7 y z w b u)))+((d2_5_1 y z w b u)*(d3_3_8 y z w b u))))))))+((-1)*(d4_8_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_5_9,d0_6_9,d0_7_8,d0_7_9,d0_8_8,d0_8_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d2_5_1,d3_3_8,d3_4_7,d3_4_8,d3_5_6,d3_5_7,d3_5_8,d3_6_6,d3_6_7,d3_6_8,d3_7_6,d3_7_7,d3_8_6,d3_8_7,d4_8_9]
  ring
#print axioms coefficient_8_9
compact_certificate_declaration theorem coefficient_8_10 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[10]?=some 0 := by
  change some ((((((d0_5_10 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_6_10 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_7_9 y z w b u)*(d1_1_1 y z w b u))+(((d0_7_10 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_8_9 y z w b u)*(d1_0_1 y z w b u))+(((d0_8_10 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_0_3 y z w b u)*(d3_8_7 y z w b u))+(((d2_1_3 y z w b u)*(d3_7_7 y z w b u))+((((d2_2_2 y z w b u)*(d3_6_8 y z w b u))+((d2_2_3 y z w b u)*(d3_6_7 y z w b u)))+((((d2_3_2 y z w b u)*(d3_5_8 y z w b u))+((d2_3_3 y z w b u)*(d3_5_7 y z w b u)))+((d2_4_2 y z w b u)*(d3_4_8 y z w b u))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_5_10,d0_6_10,d0_7_10,d0_7_9,d0_8_10,d0_8_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_1_3,d2_2_2,d2_2_3,d2_3_2,d2_3_3,d2_4_2,d3_4_8,d3_5_7,d3_5_8,d3_6_7,d3_6_8,d3_7_7,d3_8_7]
  ring
#print axioms coefficient_8_10
compact_certificate_declaration theorem coefficient_8_11 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[11]?=some 0 := by
  change some (((((d0_7_10 y z w b u)*(d1_1_1 y z w b u))+((d0_8_10 y z w b u)*(d1_0_1 y z w b u)))+(((d2_2_3 y z w b u)*(d3_6_8 y z w b u))+((d2_3_3 y z w b u)*(d3_5_8 y z w b u)))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_7_10,d0_8_10,d1_0_1,d1_1_1,d2_2_3,d2_3_3,d3_5_8,d3_6_8]
  ring
#print axioms coefficient_8_11

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_9 (y z w b u : ℂ) : (innerCertificate9 y z w b u).length=12 := by
  norm_num [innerCertificate9,add,multiply,scale,inner0_6,inner0_7,inner0_8,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner3_9,inner4_9]
compact_certificate_declaration theorem inner_eval_9 (y z w a b u : ℂ) :
    evaluate a (innerCertificate9 y z w b u)=(((((c0_6 y z w a b u)*(c1_3 y z w a b u))+(((c0_7 y z w a b u)*(c1_2 y z w a b u))+(((c0_8 y z w a b u)*(c1_1 y z w a b u))+(((c0_9 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_9 y z w a b u))+(((c2_1 y z w a b u)*(c3_8 y z w a b u))+(((c2_2 y z w a b u)*(c3_7 y z w a b u))+(((c2_3 y z w a b u)*(c3_6 y z w a b u))+(((c2_4 y z w a b u)*(c3_5 y z w a b u))+(((c2_5 y z w a b u)*(c3_4 y z w a b u))+((c2_6 y z w a b u)*(c3_3 y z w a b u)))))))))+((-1)*(c4_9 y z w a b u))) := by
  simp only [innerCertificate9,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_6,c0_7,c0_8,c0_9,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_9]
#print axioms inner_eval_9

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_9_0 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[0]?=some 0 := by
  change some (((((((d0_6_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_7_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_8_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_9_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_9_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_8_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_7_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_6_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_5_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_4_0 y z w b u))+0)+(((d2_6_0 y z w b u)*(d3_3_0 y z w b u))+0))))))))+(((-1)*(d4_9_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_6_0,d0_7_0,d0_8_0,d0_9_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d3_9_0,d4_9_0]
  ring
#print axioms coefficient_9_0
compact_certificate_declaration theorem coefficient_9_1 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[1]?=some 0 := by
  change some (((((((d0_6_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_7_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_8_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_8_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_9_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_9_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_9_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_9_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_8_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_8_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_7_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_7_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_6_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_6_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_5_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_5_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_4_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_4_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_3_1 y z w b u)))))))))+((-1)*(d4_9_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_6_1,d0_7_1,d0_8_0,d0_8_1,d0_9_0,d0_9_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d3_3_1,d3_4_0,d3_4_1,d3_5_0,d3_5_1,d3_6_0,d3_6_1,d3_7_0,d3_7_1,d3_8_0,d3_8_1,d3_9_0,d3_9_1,d4_9_1]
  ring
#print axioms coefficient_9_1
compact_certificate_declaration theorem coefficient_9_2 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[2]?=some 0 := by
  change some (((((((d0_6_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_7_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_8_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_8_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_9_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_9_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_9_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_9_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_9_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_8_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_8_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_8_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_7_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_7_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_7_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_6_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_6_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_6_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_5_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_5_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_5_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_4_2 y z w b u))+((d2_5_1 y z w b u)*(d3_4_1 y z w b u)))+((d2_6_0 y z w b u)*(d3_3_2 y z w b u)))))))))+((-1)*(d4_9_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_6_2,d0_7_2,d0_8_1,d0_8_2,d0_9_1,d0_9_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_3_2,d3_4_1,d3_4_2,d3_5_0,d3_5_1,d3_5_2,d3_6_0,d3_6_1,d3_6_2,d3_7_0,d3_7_1,d3_7_2,d3_8_0,d3_8_1,d3_8_2,d3_9_0,d3_9_1,d3_9_2,d4_9_2]
  ring
#print axioms coefficient_9_2

compact_certificate_declaration theorem coefficient_9_3 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[3]?=some 0 := by
  change some (((((((d0_6_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_7_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_8_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_8_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_9_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_9_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_9_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_9_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_9_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_9_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_8_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_8_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_8_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_8_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_7_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_7_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_7_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_7_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_6_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_6_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_6_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_6_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_5_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_5_2 y z w b u))+((d2_4_2 y z w b u)*(d3_5_1 y z w b u))))+((((d2_5_0 y z w b u)*(d3_4_3 y z w b u))+((d2_5_1 y z w b u)*(d3_4_2 y z w b u)))+((d2_6_0 y z w b u)*(d3_3_3 y z w b u)))))))))+((-1)*(d4_9_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_6_3,d0_7_3,d0_8_2,d0_8_3,d0_9_2,d0_9_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_3_3,d3_4_2,d3_4_3,d3_5_1,d3_5_2,d3_5_3,d3_6_0,d3_6_1,d3_6_2,d3_6_3,d3_7_0,d3_7_1,d3_7_2,d3_7_3,d3_8_0,d3_8_1,d3_8_2,d3_8_3,d3_9_0,d3_9_1,d3_9_2,d3_9_3,d4_9_3]
  ring
#print axioms coefficient_9_3
compact_certificate_declaration theorem coefficient_9_4 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[4]?=some 0 := by
  change some (((((((d0_6_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_7_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_8_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_8_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_9_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_9_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_9_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_9_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_9_2 y z w b u))+((d2_0_3 y z w b u)*(d3_9_1 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_8_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_8_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_8_2 y z w b u))+((d2_1_3 y z w b u)*(d3_8_1 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_7_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_7_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_7_2 y z w b u))+((d2_2_3 y z w b u)*(d3_7_1 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_6_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_6_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_6_2 y z w b u))+((d2_3_3 y z w b u)*(d3_6_1 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_5_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_5_3 y z w b u))+((d2_4_2 y z w b u)*(d3_5_2 y z w b u))))+((((d2_5_0 y z w b u)*(d3_4_4 y z w b u))+((d2_5_1 y z w b u)*(d3_4_3 y z w b u)))+((d2_6_0 y z w b u)*(d3_3_4 y z w b u)))))))))+((-1)*(d4_9_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_6_4,d0_7_4,d0_8_3,d0_8_4,d0_9_3,d0_9_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_3_4,d3_4_3,d3_4_4,d3_5_2,d3_5_3,d3_5_4,d3_6_1,d3_6_2,d3_6_3,d3_6_4,d3_7_1,d3_7_2,d3_7_3,d3_7_4,d3_8_1,d3_8_2,d3_8_3,d3_8_4,d3_9_1,d3_9_2,d3_9_3,d3_9_4,d4_9_4]
  ring
#print axioms coefficient_9_4
compact_certificate_declaration theorem coefficient_9_5 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[5]?=some 0 := by
  change some (((((((d0_6_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_7_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_8_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_8_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_9_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_9_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_9_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_9_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_9_3 y z w b u))+((d2_0_3 y z w b u)*(d3_9_2 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_8_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_8_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_8_3 y z w b u))+((d2_1_3 y z w b u)*(d3_8_2 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_7_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_7_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_7_3 y z w b u))+((d2_2_3 y z w b u)*(d3_7_2 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_6_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_6_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_6_3 y z w b u))+((d2_3_3 y z w b u)*(d3_6_2 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_5_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_5_4 y z w b u))+((d2_4_2 y z w b u)*(d3_5_3 y z w b u))))+((((d2_5_0 y z w b u)*(d3_4_5 y z w b u))+((d2_5_1 y z w b u)*(d3_4_4 y z w b u)))+((d2_6_0 y z w b u)*(d3_3_5 y z w b u)))))))))+((-1)*(d4_9_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_6_5,d0_7_5,d0_8_4,d0_8_5,d0_9_4,d0_9_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_3_5,d3_4_4,d3_4_5,d3_5_3,d3_5_4,d3_5_5,d3_6_2,d3_6_3,d3_6_4,d3_6_5,d3_7_2,d3_7_3,d3_7_4,d3_7_5,d3_8_2,d3_8_3,d3_8_4,d3_8_5,d3_9_2,d3_9_3,d3_9_4,d3_9_5,d4_9_5]
  ring
#print axioms coefficient_9_5

compact_certificate_declaration theorem coefficient_9_6 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[6]?=some 0 := by
  change some (((((((d0_6_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_7_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_8_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_8_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_9_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_9_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_9_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_9_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_9_4 y z w b u))+((d2_0_3 y z w b u)*(d3_9_3 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_8_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_8_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_8_4 y z w b u))+((d2_1_3 y z w b u)*(d3_8_3 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_7_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_7_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_7_4 y z w b u))+((d2_2_3 y z w b u)*(d3_7_3 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_6_6 y z w b u))+(((d2_3_1 y z w b u)*(d3_6_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_6_4 y z w b u))+((d2_3_3 y z w b u)*(d3_6_3 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_5_6 y z w b u))+(((d2_4_1 y z w b u)*(d3_5_5 y z w b u))+((d2_4_2 y z w b u)*(d3_5_4 y z w b u))))+((((d2_5_0 y z w b u)*(d3_4_6 y z w b u))+((d2_5_1 y z w b u)*(d3_4_5 y z w b u)))+((d2_6_0 y z w b u)*(d3_3_6 y z w b u)))))))))+((-1)*(d4_9_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_6_6,d0_7_6,d0_8_5,d0_8_6,d0_9_5,d0_9_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_3_6,d3_4_5,d3_4_6,d3_5_4,d3_5_5,d3_5_6,d3_6_3,d3_6_4,d3_6_5,d3_6_6,d3_7_3,d3_7_4,d3_7_5,d3_7_6,d3_8_3,d3_8_4,d3_8_5,d3_8_6,d3_9_3,d3_9_4,d3_9_5,d3_9_6,d4_9_6]
  ring
#print axioms coefficient_9_6
compact_certificate_declaration theorem coefficient_9_7 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[7]?=some 0 := by
  change some (((((((d0_6_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_7_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_8_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_8_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_9_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_9_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_9_7 y z w b u))+(((d2_0_1 y z w b u)*(d3_9_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_9_5 y z w b u))+((d2_0_3 y z w b u)*(d3_9_4 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_8_7 y z w b u))+(((d2_1_1 y z w b u)*(d3_8_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_8_5 y z w b u))+((d2_1_3 y z w b u)*(d3_8_4 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_7_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_7_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_7_5 y z w b u))+((d2_2_3 y z w b u)*(d3_7_4 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_6_7 y z w b u))+(((d2_3_1 y z w b u)*(d3_6_6 y z w b u))+(((d2_3_2 y z w b u)*(d3_6_5 y z w b u))+((d2_3_3 y z w b u)*(d3_6_4 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_5_7 y z w b u))+(((d2_4_1 y z w b u)*(d3_5_6 y z w b u))+((d2_4_2 y z w b u)*(d3_5_5 y z w b u))))+((((d2_5_0 y z w b u)*(d3_4_7 y z w b u))+((d2_5_1 y z w b u)*(d3_4_6 y z w b u)))+((d2_6_0 y z w b u)*(d3_3_7 y z w b u)))))))))+((-1)*(d4_9_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_6_7,d0_7_7,d0_8_6,d0_8_7,d0_9_6,d0_9_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_3_7,d3_4_6,d3_4_7,d3_5_5,d3_5_6,d3_5_7,d3_6_4,d3_6_5,d3_6_6,d3_6_7,d3_7_4,d3_7_5,d3_7_6,d3_7_7,d3_8_4,d3_8_5,d3_8_6,d3_8_7,d3_9_4,d3_9_5,d3_9_6,d3_9_7,d4_9_7]
  ring
#print axioms coefficient_9_7
compact_certificate_declaration theorem coefficient_9_8 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[8]?=some 0 := by
  change some (((((((d0_6_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_7_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_8_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_8_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_9_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_9_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_9_7 y z w b u))+(((d2_0_2 y z w b u)*(d3_9_6 y z w b u))+((d2_0_3 y z w b u)*(d3_9_5 y z w b u))))+((((d2_1_1 y z w b u)*(d3_8_7 y z w b u))+(((d2_1_2 y z w b u)*(d3_8_6 y z w b u))+((d2_1_3 y z w b u)*(d3_8_5 y z w b u))))+((((d2_2_1 y z w b u)*(d3_7_7 y z w b u))+(((d2_2_2 y z w b u)*(d3_7_6 y z w b u))+((d2_2_3 y z w b u)*(d3_7_5 y z w b u))))+((((d2_3_0 y z w b u)*(d3_6_8 y z w b u))+(((d2_3_1 y z w b u)*(d3_6_7 y z w b u))+(((d2_3_2 y z w b u)*(d3_6_6 y z w b u))+((d2_3_3 y z w b u)*(d3_6_5 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_5_8 y z w b u))+(((d2_4_1 y z w b u)*(d3_5_7 y z w b u))+((d2_4_2 y z w b u)*(d3_5_6 y z w b u))))+((((d2_5_0 y z w b u)*(d3_4_8 y z w b u))+((d2_5_1 y z w b u)*(d3_4_7 y z w b u)))+((d2_6_0 y z w b u)*(d3_3_8 y z w b u)))))))))+((-1)*(d4_9_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_6_8,d0_7_8,d0_8_7,d0_8_8,d0_9_7,d0_9_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_1_1,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_3_8,d3_4_7,d3_4_8,d3_5_6,d3_5_7,d3_5_8,d3_6_5,d3_6_6,d3_6_7,d3_6_8,d3_7_5,d3_7_6,d3_7_7,d3_8_5,d3_8_6,d3_8_7,d3_9_5,d3_9_6,d3_9_7,d4_9_8]
  ring
#print axioms coefficient_9_8

compact_certificate_declaration theorem coefficient_9_9 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[9]?=some 0 := by
  change some (((((((d0_6_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_7_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_8_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_8_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_9_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_9_9 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_9_7 y z w b u))+((d2_0_3 y z w b u)*(d3_9_6 y z w b u)))+((((d2_1_2 y z w b u)*(d3_8_7 y z w b u))+((d2_1_3 y z w b u)*(d3_8_6 y z w b u)))+((((d2_2_2 y z w b u)*(d3_7_7 y z w b u))+((d2_2_3 y z w b u)*(d3_7_6 y z w b u)))+((((d2_3_1 y z w b u)*(d3_6_8 y z w b u))+(((d2_3_2 y z w b u)*(d3_6_7 y z w b u))+((d2_3_3 y z w b u)*(d3_6_6 y z w b u))))+((((d2_4_1 y z w b u)*(d3_5_8 y z w b u))+((d2_4_2 y z w b u)*(d3_5_7 y z w b u)))+((d2_5_1 y z w b u)*(d3_4_8 y z w b u))))))))+((-1)*(d4_9_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_6_9,d0_7_9,d0_8_8,d0_8_9,d0_9_8,d0_9_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_1_2,d2_1_3,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d2_5_1,d3_4_8,d3_5_7,d3_5_8,d3_6_6,d3_6_7,d3_6_8,d3_7_6,d3_7_7,d3_8_6,d3_8_7,d3_9_6,d3_9_7,d4_9_9]
  ring
#print axioms coefficient_9_9
compact_certificate_declaration theorem coefficient_9_10 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[10]?=some 0 := by
  change some ((((((d0_6_10 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_7_10 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_8_9 y z w b u)*(d1_1_1 y z w b u))+(((d0_8_10 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_9_9 y z w b u)*(d1_0_1 y z w b u)))))+(((d2_0_3 y z w b u)*(d3_9_7 y z w b u))+(((d2_1_3 y z w b u)*(d3_8_7 y z w b u))+(((d2_2_3 y z w b u)*(d3_7_7 y z w b u))+((((d2_3_2 y z w b u)*(d3_6_8 y z w b u))+((d2_3_3 y z w b u)*(d3_6_7 y z w b u)))+((d2_4_2 y z w b u)*(d3_5_8 y z w b u))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_6_10,d0_7_10,d0_8_10,d0_8_9,d0_9_9,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_1_3,d2_2_3,d2_3_2,d2_3_3,d2_4_2,d3_5_8,d3_6_7,d3_6_8,d3_7_7,d3_8_7,d3_9_7]
  ring
#print axioms coefficient_9_10
compact_certificate_declaration theorem coefficient_9_11 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[11]?=some 0 := by
  change some ((((d0_8_10 y z w b u)*(d1_1_1 y z w b u))+((d2_3_3 y z w b u)*(d3_6_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_8_10,d1_1_1,d2_3_3,d3_6_8]
  ring
#print axioms coefficient_9_11

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_10 (y z w b u : ℂ) : (innerCertificate10 y z w b u).length=11 := by
  norm_num [innerCertificate10,add,multiply,scale,inner0_10,inner0_7,inner0_8,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_10,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner3_9,inner4_10]
compact_certificate_declaration theorem inner_eval_10 (y z w a b u : ℂ) :
    evaluate a (innerCertificate10 y z w b u)=(((((c0_7 y z w a b u)*(c1_3 y z w a b u))+(((c0_8 y z w a b u)*(c1_2 y z w a b u))+(((c0_9 y z w a b u)*(c1_1 y z w a b u))+(((c0_10 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_10 y z w a b u))+(((c2_1 y z w a b u)*(c3_9 y z w a b u))+(((c2_2 y z w a b u)*(c3_8 y z w a b u))+(((c2_3 y z w a b u)*(c3_7 y z w a b u))+(((c2_4 y z w a b u)*(c3_6 y z w a b u))+(((c2_5 y z w a b u)*(c3_5 y z w a b u))+((c2_6 y z w a b u)*(c3_4 y z w a b u)))))))))+((-1)*(c4_10 y z w a b u))) := by
  simp only [innerCertificate10,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_10,c0_7,c0_8,c0_9,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c3_10,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_10]
#print axioms inner_eval_10

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_10_0 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[0]?=some 0 := by
  change some (((((((d0_7_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_8_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_9_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_10_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_10_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_9_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_8_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_7_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_6_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_5_0 y z w b u))+0)+(((d2_6_0 y z w b u)*(d3_4_0 y z w b u))+0))))))))+(((-1)*(d4_10_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_7_0,d0_8_0,d0_9_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d3_10_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d3_9_0,d4_10_0]
  ring
#print axioms coefficient_10_0
compact_certificate_declaration theorem coefficient_10_1 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[1]?=some 0 := by
  change some (((((((d0_7_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_8_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_9_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_9_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_10_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_10_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_10_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_10_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_9_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_9_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_8_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_8_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_7_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_7_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_6_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_6_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_5_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_5_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_4_1 y z w b u)))))))))+((-1)*(d4_10_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_10_1,d0_7_1,d0_8_1,d0_9_0,d0_9_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d3_10_0,d3_10_1,d3_4_1,d3_5_0,d3_5_1,d3_6_0,d3_6_1,d3_7_0,d3_7_1,d3_8_0,d3_8_1,d3_9_0,d3_9_1,d4_10_1]
  ring
#print axioms coefficient_10_1
compact_certificate_declaration theorem coefficient_10_2 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[2]?=some 0 := by
  change some (((((((d0_7_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_8_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_9_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_9_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_10_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_10_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_10_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_10_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_10_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_9_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_9_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_9_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_8_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_8_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_8_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_7_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_7_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_7_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_6_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_6_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_6_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_5_2 y z w b u))+((d2_5_1 y z w b u)*(d3_5_1 y z w b u)))+((d2_6_0 y z w b u)*(d3_4_2 y z w b u)))))))))+((-1)*(d4_10_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_1,d0_10_2,d0_7_2,d0_8_2,d0_9_1,d0_9_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_0,d3_10_1,d3_10_2,d3_4_2,d3_5_1,d3_5_2,d3_6_0,d3_6_1,d3_6_2,d3_7_0,d3_7_1,d3_7_2,d3_8_0,d3_8_1,d3_8_2,d3_9_0,d3_9_1,d3_9_2,d4_10_2]
  ring
#print axioms coefficient_10_2

compact_certificate_declaration theorem coefficient_10_3 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[3]?=some 0 := by
  change some (((((((d0_7_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_8_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_9_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_9_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_10_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_10_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_10_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_10_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_10_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_10_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_9_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_9_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_9_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_9_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_8_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_8_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_8_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_8_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_7_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_7_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_7_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_7_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_6_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_6_2 y z w b u))+((d2_4_2 y z w b u)*(d3_6_1 y z w b u))))+((((d2_5_0 y z w b u)*(d3_5_3 y z w b u))+((d2_5_1 y z w b u)*(d3_5_2 y z w b u)))+((d2_6_0 y z w b u)*(d3_4_3 y z w b u)))))))))+((-1)*(d4_10_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_2,d0_10_3,d0_7_3,d0_8_3,d0_9_2,d0_9_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_0,d3_10_1,d3_10_2,d3_10_3,d3_4_3,d3_5_2,d3_5_3,d3_6_1,d3_6_2,d3_6_3,d3_7_0,d3_7_1,d3_7_2,d3_7_3,d3_8_0,d3_8_1,d3_8_2,d3_8_3,d3_9_0,d3_9_1,d3_9_2,d3_9_3,d4_10_3]
  ring
#print axioms coefficient_10_3
compact_certificate_declaration theorem coefficient_10_4 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[4]?=some 0 := by
  change some (((((((d0_7_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_8_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_9_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_9_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_10_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_10_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_10_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_10_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_10_2 y z w b u))+((d2_0_3 y z w b u)*(d3_10_1 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_9_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_9_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_9_2 y z w b u))+((d2_1_3 y z w b u)*(d3_9_1 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_8_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_8_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_8_2 y z w b u))+((d2_2_3 y z w b u)*(d3_8_1 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_7_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_7_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_7_2 y z w b u))+((d2_3_3 y z w b u)*(d3_7_1 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_6_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_6_3 y z w b u))+((d2_4_2 y z w b u)*(d3_6_2 y z w b u))))+((((d2_5_0 y z w b u)*(d3_5_4 y z w b u))+((d2_5_1 y z w b u)*(d3_5_3 y z w b u)))+((d2_6_0 y z w b u)*(d3_4_4 y z w b u)))))))))+((-1)*(d4_10_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_3,d0_10_4,d0_7_4,d0_8_4,d0_9_3,d0_9_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_1,d3_10_2,d3_10_3,d3_10_4,d3_4_4,d3_5_3,d3_5_4,d3_6_2,d3_6_3,d3_6_4,d3_7_1,d3_7_2,d3_7_3,d3_7_4,d3_8_1,d3_8_2,d3_8_3,d3_8_4,d3_9_1,d3_9_2,d3_9_3,d3_9_4,d4_10_4]
  ring
#print axioms coefficient_10_4
compact_certificate_declaration theorem coefficient_10_5 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[5]?=some 0 := by
  change some (((((((d0_7_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_8_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_9_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_9_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_10_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_10_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_10_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_10_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_10_3 y z w b u))+((d2_0_3 y z w b u)*(d3_10_2 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_9_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_9_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_9_3 y z w b u))+((d2_1_3 y z w b u)*(d3_9_2 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_8_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_8_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_8_3 y z w b u))+((d2_2_3 y z w b u)*(d3_8_2 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_7_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_7_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_7_3 y z w b u))+((d2_3_3 y z w b u)*(d3_7_2 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_6_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_6_4 y z w b u))+((d2_4_2 y z w b u)*(d3_6_3 y z w b u))))+((((d2_5_0 y z w b u)*(d3_5_5 y z w b u))+((d2_5_1 y z w b u)*(d3_5_4 y z w b u)))+((d2_6_0 y z w b u)*(d3_4_5 y z w b u)))))))))+((-1)*(d4_10_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_4,d0_10_5,d0_7_5,d0_8_5,d0_9_4,d0_9_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_2,d3_10_3,d3_10_4,d3_10_5,d3_4_5,d3_5_4,d3_5_5,d3_6_3,d3_6_4,d3_6_5,d3_7_2,d3_7_3,d3_7_4,d3_7_5,d3_8_2,d3_8_3,d3_8_4,d3_8_5,d3_9_2,d3_9_3,d3_9_4,d3_9_5,d4_10_5]
  ring
#print axioms coefficient_10_5

compact_certificate_declaration theorem coefficient_10_6 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[6]?=some 0 := by
  change some (((((((d0_7_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_8_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_9_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_9_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_10_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_10_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_10_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_10_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_10_4 y z w b u))+((d2_0_3 y z w b u)*(d3_10_3 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_9_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_9_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_9_4 y z w b u))+((d2_1_3 y z w b u)*(d3_9_3 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_8_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_8_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_8_4 y z w b u))+((d2_2_3 y z w b u)*(d3_8_3 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_7_6 y z w b u))+(((d2_3_1 y z w b u)*(d3_7_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_7_4 y z w b u))+((d2_3_3 y z w b u)*(d3_7_3 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_6_6 y z w b u))+(((d2_4_1 y z w b u)*(d3_6_5 y z w b u))+((d2_4_2 y z w b u)*(d3_6_4 y z w b u))))+((((d2_5_0 y z w b u)*(d3_5_6 y z w b u))+((d2_5_1 y z w b u)*(d3_5_5 y z w b u)))+((d2_6_0 y z w b u)*(d3_4_6 y z w b u)))))))))+((-1)*(d4_10_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_5,d0_10_6,d0_7_6,d0_8_6,d0_9_5,d0_9_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_3,d3_10_4,d3_10_5,d3_10_6,d3_4_6,d3_5_5,d3_5_6,d3_6_4,d3_6_5,d3_6_6,d3_7_3,d3_7_4,d3_7_5,d3_7_6,d3_8_3,d3_8_4,d3_8_5,d3_8_6,d3_9_3,d3_9_4,d3_9_5,d3_9_6,d4_10_6]
  ring
#print axioms coefficient_10_6
compact_certificate_declaration theorem coefficient_10_7 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[7]?=some 0 := by
  change some (((((((d0_7_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_8_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_9_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_9_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_10_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_10_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_10_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_10_5 y z w b u))+((d2_0_3 y z w b u)*(d3_10_4 y z w b u))))+((((d2_1_0 y z w b u)*(d3_9_7 y z w b u))+(((d2_1_1 y z w b u)*(d3_9_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_9_5 y z w b u))+((d2_1_3 y z w b u)*(d3_9_4 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_8_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_8_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_8_5 y z w b u))+((d2_2_3 y z w b u)*(d3_8_4 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_7_7 y z w b u))+(((d2_3_1 y z w b u)*(d3_7_6 y z w b u))+(((d2_3_2 y z w b u)*(d3_7_5 y z w b u))+((d2_3_3 y z w b u)*(d3_7_4 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_6_7 y z w b u))+(((d2_4_1 y z w b u)*(d3_6_6 y z w b u))+((d2_4_2 y z w b u)*(d3_6_5 y z w b u))))+((((d2_5_0 y z w b u)*(d3_5_7 y z w b u))+((d2_5_1 y z w b u)*(d3_5_6 y z w b u)))+((d2_6_0 y z w b u)*(d3_4_7 y z w b u)))))))))+((-1)*(d4_10_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_6,d0_10_7,d0_7_7,d0_8_7,d0_9_6,d0_9_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_4,d3_10_5,d3_10_6,d3_4_7,d3_5_6,d3_5_7,d3_6_5,d3_6_6,d3_6_7,d3_7_4,d3_7_5,d3_7_6,d3_7_7,d3_8_4,d3_8_5,d3_8_6,d3_8_7,d3_9_4,d3_9_5,d3_9_6,d3_9_7,d4_10_7]
  ring
#print axioms coefficient_10_7
compact_certificate_declaration theorem coefficient_10_8 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[8]?=some 0 := by
  change some (((((((d0_7_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_8_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_9_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_9_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_10_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_10_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_10_6 y z w b u))+((d2_0_3 y z w b u)*(d3_10_5 y z w b u)))+((((d2_1_1 y z w b u)*(d3_9_7 y z w b u))+(((d2_1_2 y z w b u)*(d3_9_6 y z w b u))+((d2_1_3 y z w b u)*(d3_9_5 y z w b u))))+((((d2_2_1 y z w b u)*(d3_8_7 y z w b u))+(((d2_2_2 y z w b u)*(d3_8_6 y z w b u))+((d2_2_3 y z w b u)*(d3_8_5 y z w b u))))+((((d2_3_1 y z w b u)*(d3_7_7 y z w b u))+(((d2_3_2 y z w b u)*(d3_7_6 y z w b u))+((d2_3_3 y z w b u)*(d3_7_5 y z w b u))))+((((d2_4_0 y z w b u)*(d3_6_8 y z w b u))+(((d2_4_1 y z w b u)*(d3_6_7 y z w b u))+((d2_4_2 y z w b u)*(d3_6_6 y z w b u))))+((((d2_5_0 y z w b u)*(d3_5_8 y z w b u))+((d2_5_1 y z w b u)*(d3_5_7 y z w b u)))+((d2_6_0 y z w b u)*(d3_4_8 y z w b u)))))))))+((-1)*(d4_10_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_7,d0_10_8,d0_7_8,d0_8_8,d0_9_7,d0_9_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_1_1,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_5,d3_10_6,d3_4_8,d3_5_7,d3_5_8,d3_6_6,d3_6_7,d3_6_8,d3_7_5,d3_7_6,d3_7_7,d3_8_5,d3_8_6,d3_8_7,d3_9_5,d3_9_6,d3_9_7,d4_10_8]
  ring
#print axioms coefficient_10_8

compact_certificate_declaration theorem coefficient_10_9 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[9]?=some 0 := by
  change some (((((((d0_7_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_8_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_9_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_9_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_10_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_10_9 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_0_3 y z w b u)*(d3_10_6 y z w b u))+((((d2_1_2 y z w b u)*(d3_9_7 y z w b u))+((d2_1_3 y z w b u)*(d3_9_6 y z w b u)))+((((d2_2_2 y z w b u)*(d3_8_7 y z w b u))+((d2_2_3 y z w b u)*(d3_8_6 y z w b u)))+((((d2_3_2 y z w b u)*(d3_7_7 y z w b u))+((d2_3_3 y z w b u)*(d3_7_6 y z w b u)))+((((d2_4_1 y z w b u)*(d3_6_8 y z w b u))+((d2_4_2 y z w b u)*(d3_6_7 y z w b u)))+((d2_5_1 y z w b u)*(d3_5_8 y z w b u))))))))+((-1)*(d4_10_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_8,d0_10_9,d0_7_9,d0_8_9,d0_9_8,d0_9_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_1_2,d2_1_3,d2_2_2,d2_2_3,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d2_5_1,d3_10_6,d3_5_8,d3_6_7,d3_6_8,d3_7_6,d3_7_7,d3_8_6,d3_8_7,d3_9_6,d3_9_7,d4_10_9]
  ring
#print axioms coefficient_10_9
compact_certificate_declaration theorem coefficient_10_10 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[10]?=some 0 := by
  change some ((((((d0_7_10 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_8_10 y z w b u)*(d1_2_0 y z w b u))+0)+(((d0_9_9 y z w b u)*(d1_1_1 y z w b u))+((d0_10_9 y z w b u)*(d1_0_1 y z w b u)))))+(((d2_1_3 y z w b u)*(d3_9_7 y z w b u))+(((d2_2_3 y z w b u)*(d3_8_7 y z w b u))+(((d2_3_3 y z w b u)*(d3_7_7 y z w b u))+((d2_4_2 y z w b u)*(d3_6_8 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_9,d0_7_10,d0_8_10,d0_9_9,d1_0_1,d1_1_1,d1_2_0,d1_3_0,d2_1_3,d2_2_3,d2_3_3,d2_4_2,d3_6_8,d3_7_7,d3_8_7,d3_9_7]
  ring
#print axioms coefficient_10_10

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_11 (y z w b u : ℂ) : (innerCertificate11 y z w b u).length=11 := by
  norm_num [innerCertificate11,add,multiply,scale,inner0_10,inner0_11,inner0_8,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_10,inner3_11,inner3_5,inner3_6,inner3_7,inner3_8,inner3_9,inner4_11]
compact_certificate_declaration theorem inner_eval_11 (y z w a b u : ℂ) :
    evaluate a (innerCertificate11 y z w b u)=(((((c0_8 y z w a b u)*(c1_3 y z w a b u))+(((c0_9 y z w a b u)*(c1_2 y z w a b u))+(((c0_10 y z w a b u)*(c1_1 y z w a b u))+(((c0_11 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_11 y z w a b u))+(((c2_1 y z w a b u)*(c3_10 y z w a b u))+(((c2_2 y z w a b u)*(c3_9 y z w a b u))+(((c2_3 y z w a b u)*(c3_8 y z w a b u))+(((c2_4 y z w a b u)*(c3_7 y z w a b u))+(((c2_5 y z w a b u)*(c3_6 y z w a b u))+((c2_6 y z w a b u)*(c3_5 y z w a b u)))))))))+((-1)*(c4_11 y z w a b u))) := by
  simp only [innerCertificate11,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_10,c0_11,c0_8,c0_9,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c3_10,c3_11,c3_5,c3_6,c3_7,c3_8,c3_9,c4_11]
#print axioms inner_eval_11

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_11_0 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[0]?=some 0 := by
  change some (((((((d0_8_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_9_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_10_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_11_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_11_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_10_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_9_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_8_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_7_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_6_0 y z w b u))+0)+(((d2_6_0 y z w b u)*(d3_5_0 y z w b u))+0))))))))+(((-1)*(d4_11_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_11_0,d0_8_0,d0_9_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d3_10_0,d3_11_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d3_9_0,d4_11_0]
  ring
#print axioms coefficient_11_0
compact_certificate_declaration theorem coefficient_11_1 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[1]?=some 0 := by
  change some (((((((d0_8_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_9_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_10_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_10_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_11_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_11_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_11_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_11_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_10_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_10_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_9_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_9_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_8_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_8_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_7_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_7_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_6_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_6_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_5_1 y z w b u)))))))))+((-1)*(d4_11_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_10_1,d0_11_0,d0_11_1,d0_8_1,d0_9_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d3_10_0,d3_10_1,d3_11_0,d3_11_1,d3_5_1,d3_6_0,d3_6_1,d3_7_0,d3_7_1,d3_8_0,d3_8_1,d3_9_0,d3_9_1,d4_11_1]
  ring
#print axioms coefficient_11_1
compact_certificate_declaration theorem coefficient_11_2 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[2]?=some 0 := by
  change some (((((((d0_8_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_9_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_10_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_10_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_11_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_11_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_11_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_11_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_11_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_10_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_10_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_10_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_9_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_9_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_9_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_8_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_8_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_8_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_7_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_7_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_7_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_6_2 y z w b u))+((d2_5_1 y z w b u)*(d3_6_1 y z w b u)))+((d2_6_0 y z w b u)*(d3_5_2 y z w b u)))))))))+((-1)*(d4_11_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_1,d0_10_2,d0_11_1,d0_11_2,d0_8_2,d0_9_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_0,d3_10_1,d3_10_2,d3_11_0,d3_11_1,d3_11_2,d3_5_2,d3_6_1,d3_6_2,d3_7_0,d3_7_1,d3_7_2,d3_8_0,d3_8_1,d3_8_2,d3_9_0,d3_9_1,d3_9_2,d4_11_2]
  ring
#print axioms coefficient_11_2

compact_certificate_declaration theorem coefficient_11_3 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[3]?=some 0 := by
  change some (((((((d0_8_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_9_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_10_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_10_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_11_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_11_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_11_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_11_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_11_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_11_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_10_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_10_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_10_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_10_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_9_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_9_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_9_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_9_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_8_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_8_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_8_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_8_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_7_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_7_2 y z w b u))+((d2_4_2 y z w b u)*(d3_7_1 y z w b u))))+((((d2_5_0 y z w b u)*(d3_6_3 y z w b u))+((d2_5_1 y z w b u)*(d3_6_2 y z w b u)))+((d2_6_0 y z w b u)*(d3_5_3 y z w b u)))))))))+((-1)*(d4_11_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_2,d0_10_3,d0_11_2,d0_11_3,d0_8_3,d0_9_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_0,d3_10_1,d3_10_2,d3_10_3,d3_11_0,d3_11_1,d3_11_2,d3_11_3,d3_5_3,d3_6_2,d3_6_3,d3_7_1,d3_7_2,d3_7_3,d3_8_0,d3_8_1,d3_8_2,d3_8_3,d3_9_0,d3_9_1,d3_9_2,d3_9_3,d4_11_3]
  ring
#print axioms coefficient_11_3
compact_certificate_declaration theorem coefficient_11_4 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[4]?=some 0 := by
  change some (((((((d0_8_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_9_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_10_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_10_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_11_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_11_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_11_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_11_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_11_2 y z w b u))+((d2_0_3 y z w b u)*(d3_11_1 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_10_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_10_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_10_2 y z w b u))+((d2_1_3 y z w b u)*(d3_10_1 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_9_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_9_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_9_2 y z w b u))+((d2_2_3 y z w b u)*(d3_9_1 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_8_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_8_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_8_2 y z w b u))+((d2_3_3 y z w b u)*(d3_8_1 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_7_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_7_3 y z w b u))+((d2_4_2 y z w b u)*(d3_7_2 y z w b u))))+((((d2_5_0 y z w b u)*(d3_6_4 y z w b u))+((d2_5_1 y z w b u)*(d3_6_3 y z w b u)))+((d2_6_0 y z w b u)*(d3_5_4 y z w b u)))))))))+((-1)*(d4_11_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_3,d0_10_4,d0_11_3,d0_11_4,d0_8_4,d0_9_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_1,d3_10_2,d3_10_3,d3_10_4,d3_11_1,d3_11_2,d3_11_3,d3_11_4,d3_5_4,d3_6_3,d3_6_4,d3_7_2,d3_7_3,d3_7_4,d3_8_1,d3_8_2,d3_8_3,d3_8_4,d3_9_1,d3_9_2,d3_9_3,d3_9_4,d4_11_4]
  ring
#print axioms coefficient_11_4
compact_certificate_declaration theorem coefficient_11_5 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[5]?=some 0 := by
  change some (((((((d0_8_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_9_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_10_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_10_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_11_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_11_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_11_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_11_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_11_3 y z w b u))+((d2_0_3 y z w b u)*(d3_11_2 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_10_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_10_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_10_3 y z w b u))+((d2_1_3 y z w b u)*(d3_10_2 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_9_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_9_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_9_3 y z w b u))+((d2_2_3 y z w b u)*(d3_9_2 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_8_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_8_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_8_3 y z w b u))+((d2_3_3 y z w b u)*(d3_8_2 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_7_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_7_4 y z w b u))+((d2_4_2 y z w b u)*(d3_7_3 y z w b u))))+((((d2_5_0 y z w b u)*(d3_6_5 y z w b u))+((d2_5_1 y z w b u)*(d3_6_4 y z w b u)))+((d2_6_0 y z w b u)*(d3_5_5 y z w b u)))))))))+((-1)*(d4_11_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_4,d0_10_5,d0_11_4,d0_11_5,d0_8_5,d0_9_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_2,d3_10_3,d3_10_4,d3_10_5,d3_11_2,d3_11_3,d3_11_4,d3_11_5,d3_5_5,d3_6_4,d3_6_5,d3_7_3,d3_7_4,d3_7_5,d3_8_2,d3_8_3,d3_8_4,d3_8_5,d3_9_2,d3_9_3,d3_9_4,d3_9_5,d4_11_5]
  ring
#print axioms coefficient_11_5

compact_certificate_declaration theorem coefficient_11_6 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[6]?=some 0 := by
  change some (((((((d0_8_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_9_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_10_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_10_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_11_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_11_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_11_6 y z w b u))+(((d2_0_1 y z w b u)*(d3_11_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_11_4 y z w b u))+((d2_0_3 y z w b u)*(d3_11_3 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_10_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_10_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_10_4 y z w b u))+((d2_1_3 y z w b u)*(d3_10_3 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_9_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_9_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_9_4 y z w b u))+((d2_2_3 y z w b u)*(d3_9_3 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_8_6 y z w b u))+(((d2_3_1 y z w b u)*(d3_8_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_8_4 y z w b u))+((d2_3_3 y z w b u)*(d3_8_3 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_7_6 y z w b u))+(((d2_4_1 y z w b u)*(d3_7_5 y z w b u))+((d2_4_2 y z w b u)*(d3_7_4 y z w b u))))+((((d2_5_0 y z w b u)*(d3_6_6 y z w b u))+((d2_5_1 y z w b u)*(d3_6_5 y z w b u)))+((d2_6_0 y z w b u)*(d3_5_6 y z w b u)))))))))+((-1)*(d4_11_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_5,d0_10_6,d0_11_5,d0_11_6,d0_8_6,d0_9_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_3,d3_10_4,d3_10_5,d3_10_6,d3_11_3,d3_11_4,d3_11_5,d3_11_6,d3_5_6,d3_6_5,d3_6_6,d3_7_4,d3_7_5,d3_7_6,d3_8_3,d3_8_4,d3_8_5,d3_8_6,d3_9_3,d3_9_4,d3_9_5,d3_9_6,d4_11_6]
  ring
#print axioms coefficient_11_6
compact_certificate_declaration theorem coefficient_11_7 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[7]?=some 0 := by
  change some (((((((d0_8_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_9_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_10_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_10_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_11_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_11_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_11_6 y z w b u))+(((d2_0_2 y z w b u)*(d3_11_5 y z w b u))+((d2_0_3 y z w b u)*(d3_11_4 y z w b u))))+((((d2_1_1 y z w b u)*(d3_10_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_10_5 y z w b u))+((d2_1_3 y z w b u)*(d3_10_4 y z w b u))))+((((d2_2_0 y z w b u)*(d3_9_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_9_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_9_5 y z w b u))+((d2_2_3 y z w b u)*(d3_9_4 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_8_7 y z w b u))+(((d2_3_1 y z w b u)*(d3_8_6 y z w b u))+(((d2_3_2 y z w b u)*(d3_8_5 y z w b u))+((d2_3_3 y z w b u)*(d3_8_4 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_7_7 y z w b u))+(((d2_4_1 y z w b u)*(d3_7_6 y z w b u))+((d2_4_2 y z w b u)*(d3_7_5 y z w b u))))+((((d2_5_0 y z w b u)*(d3_6_7 y z w b u))+((d2_5_1 y z w b u)*(d3_6_6 y z w b u)))+((d2_6_0 y z w b u)*(d3_5_7 y z w b u)))))))))+((-1)*(d4_11_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_6,d0_10_7,d0_11_6,d0_11_7,d0_8_7,d0_9_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_4,d3_10_5,d3_10_6,d3_11_4,d3_11_5,d3_11_6,d3_5_7,d3_6_6,d3_6_7,d3_7_5,d3_7_6,d3_7_7,d3_8_4,d3_8_5,d3_8_6,d3_8_7,d3_9_4,d3_9_5,d3_9_6,d3_9_7,d4_11_7]
  ring
#print axioms coefficient_11_7
compact_certificate_declaration theorem coefficient_11_8 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[8]?=some 0 := by
  change some (((((((d0_8_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_9_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_10_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_10_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_11_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_11_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_11_6 y z w b u))+((d2_0_3 y z w b u)*(d3_11_5 y z w b u)))+((((d2_1_2 y z w b u)*(d3_10_6 y z w b u))+((d2_1_3 y z w b u)*(d3_10_5 y z w b u)))+((((d2_2_1 y z w b u)*(d3_9_7 y z w b u))+(((d2_2_2 y z w b u)*(d3_9_6 y z w b u))+((d2_2_3 y z w b u)*(d3_9_5 y z w b u))))+((((d2_3_1 y z w b u)*(d3_8_7 y z w b u))+(((d2_3_2 y z w b u)*(d3_8_6 y z w b u))+((d2_3_3 y z w b u)*(d3_8_5 y z w b u))))+((((d2_4_1 y z w b u)*(d3_7_7 y z w b u))+((d2_4_2 y z w b u)*(d3_7_6 y z w b u)))+((((d2_5_0 y z w b u)*(d3_6_8 y z w b u))+((d2_5_1 y z w b u)*(d3_6_7 y z w b u)))+((d2_6_0 y z w b u)*(d3_5_8 y z w b u)))))))))+((-1)*(d4_11_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_7,d0_10_8,d0_11_7,d0_11_8,d0_8_8,d0_9_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_5,d3_10_6,d3_11_5,d3_11_6,d3_5_8,d3_6_7,d3_6_8,d3_7_6,d3_7_7,d3_8_5,d3_8_6,d3_8_7,d3_9_5,d3_9_6,d3_9_7,d4_11_8]
  ring
#print axioms coefficient_11_8

compact_certificate_declaration theorem coefficient_11_9 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[9]?=some 0 := by
  change some ((((((d0_8_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_9_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_10_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_10_9 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_11_8 y z w b u)*(d1_0_1 y z w b u))+(((d0_11_9 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_0_3 y z w b u)*(d3_11_6 y z w b u))+(((d2_1_3 y z w b u)*(d3_10_6 y z w b u))+((((d2_2_2 y z w b u)*(d3_9_7 y z w b u))+((d2_2_3 y z w b u)*(d3_9_6 y z w b u)))+((((d2_3_2 y z w b u)*(d3_8_7 y z w b u))+((d2_3_3 y z w b u)*(d3_8_6 y z w b u)))+(((d2_4_2 y z w b u)*(d3_7_7 y z w b u))+((d2_5_1 y z w b u)*(d3_6_8 y z w b u)))))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_8,d0_10_9,d0_11_8,d0_11_9,d0_8_9,d0_9_9,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_1_3,d2_2_2,d2_2_3,d2_3_2,d2_3_3,d2_4_2,d2_5_1,d3_10_6,d3_11_6,d3_6_8,d3_7_7,d3_8_6,d3_8_7,d3_9_6,d3_9_7]
  ring
#print axioms coefficient_11_9
compact_certificate_declaration theorem coefficient_11_10 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[10]?=some 0 := by
  change some ((((((d0_8_10 y z w b u)*(d1_3_0 y z w b u))+0)+(((d0_10_9 y z w b u)*(d1_1_1 y z w b u))+((d0_11_9 y z w b u)*(d1_0_1 y z w b u))))+(((d2_2_3 y z w b u)*(d3_9_7 y z w b u))+((d2_3_3 y z w b u)*(d3_8_7 y z w b u)))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_9,d0_11_9,d0_8_10,d1_0_1,d1_1_1,d1_3_0,d2_2_3,d2_3_3,d3_8_7,d3_9_7]
  ring
#print axioms coefficient_11_10

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_12 (y z w b u : ℂ) : (innerCertificate12 y z w b u).length=11 := by
  norm_num [innerCertificate12,add,multiply,scale,inner0_10,inner0_11,inner0_12,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_10,inner3_11,inner3_12,inner3_6,inner3_7,inner3_8,inner3_9,inner4_12]
compact_certificate_declaration theorem inner_eval_12 (y z w a b u : ℂ) :
    evaluate a (innerCertificate12 y z w b u)=(((((c0_9 y z w a b u)*(c1_3 y z w a b u))+(((c0_10 y z w a b u)*(c1_2 y z w a b u))+(((c0_11 y z w a b u)*(c1_1 y z w a b u))+(((c0_12 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_12 y z w a b u))+(((c2_1 y z w a b u)*(c3_11 y z w a b u))+(((c2_2 y z w a b u)*(c3_10 y z w a b u))+(((c2_3 y z w a b u)*(c3_9 y z w a b u))+(((c2_4 y z w a b u)*(c3_8 y z w a b u))+(((c2_5 y z w a b u)*(c3_7 y z w a b u))+((c2_6 y z w a b u)*(c3_6 y z w a b u)))))))))+((-1)*(c4_12 y z w a b u))) := by
  simp only [innerCertificate12,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_10,c0_11,c0_12,c0_9,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c3_10,c3_11,c3_12,c3_6,c3_7,c3_8,c3_9,c4_12]
#print axioms inner_eval_12

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_12_0 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[0]?=some 0 := by
  change some (((((((d0_9_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_10_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_11_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_12_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_12_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_11_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_10_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_9_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_8_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_7_0 y z w b u))+0)+(((d2_6_0 y z w b u)*(d3_6_0 y z w b u))+0))))))))+(((-1)*(d4_12_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_11_0,d0_12_0,d0_9_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d3_10_0,d3_11_0,d3_12_0,d3_6_0,d3_7_0,d3_8_0,d3_9_0,d4_12_0]
  ring
#print axioms coefficient_12_0
compact_certificate_declaration theorem coefficient_12_1 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[1]?=some 0 := by
  change some (((((((d0_9_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_10_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_11_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_11_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_12_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_12_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_12_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_12_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_11_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_11_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_10_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_10_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_9_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_9_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_8_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_8_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_7_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_7_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_6_1 y z w b u)))))))))+((-1)*(d4_12_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_1,d0_11_0,d0_11_1,d0_12_0,d0_12_1,d0_9_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d3_10_0,d3_10_1,d3_11_0,d3_11_1,d3_12_0,d3_12_1,d3_6_1,d3_7_0,d3_7_1,d3_8_0,d3_8_1,d3_9_0,d3_9_1,d4_12_1]
  ring
#print axioms coefficient_12_1
compact_certificate_declaration theorem coefficient_12_2 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[2]?=some 0 := by
  change some (((((((d0_9_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_10_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_11_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_11_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_12_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_12_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_12_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_12_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_12_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_11_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_11_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_11_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_10_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_10_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_10_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_9_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_9_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_9_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_8_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_8_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_8_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_7_2 y z w b u))+((d2_5_1 y z w b u)*(d3_7_1 y z w b u)))+((d2_6_0 y z w b u)*(d3_6_2 y z w b u)))))))))+((-1)*(d4_12_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_2,d0_11_1,d0_11_2,d0_12_1,d0_12_2,d0_9_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_0,d3_10_1,d3_10_2,d3_11_0,d3_11_1,d3_11_2,d3_12_0,d3_12_1,d3_12_2,d3_6_2,d3_7_1,d3_7_2,d3_8_0,d3_8_1,d3_8_2,d3_9_0,d3_9_1,d3_9_2,d4_12_2]
  ring
#print axioms coefficient_12_2

compact_certificate_declaration theorem coefficient_12_3 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[3]?=some 0 := by
  change some (((((((d0_9_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_10_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_11_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_11_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_12_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_12_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_12_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_12_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_12_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_12_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_11_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_11_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_11_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_11_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_10_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_10_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_10_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_10_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_9_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_9_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_9_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_9_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_8_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_8_2 y z w b u))+((d2_4_2 y z w b u)*(d3_8_1 y z w b u))))+((((d2_5_0 y z w b u)*(d3_7_3 y z w b u))+((d2_5_1 y z w b u)*(d3_7_2 y z w b u)))+((d2_6_0 y z w b u)*(d3_6_3 y z w b u)))))))))+((-1)*(d4_12_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_3,d0_11_2,d0_11_3,d0_12_2,d0_12_3,d0_9_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_0,d3_10_1,d3_10_2,d3_10_3,d3_11_0,d3_11_1,d3_11_2,d3_11_3,d3_12_0,d3_12_1,d3_12_2,d3_12_3,d3_6_3,d3_7_2,d3_7_3,d3_8_1,d3_8_2,d3_8_3,d3_9_0,d3_9_1,d3_9_2,d3_9_3,d4_12_3]
  ring
#print axioms coefficient_12_3
compact_certificate_declaration theorem coefficient_12_4 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[4]?=some 0 := by
  change some (((((((d0_9_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_10_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_11_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_11_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_12_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_12_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_12_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_12_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_12_2 y z w b u))+((d2_0_3 y z w b u)*(d3_12_1 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_11_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_11_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_11_2 y z w b u))+((d2_1_3 y z w b u)*(d3_11_1 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_10_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_10_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_10_2 y z w b u))+((d2_2_3 y z w b u)*(d3_10_1 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_9_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_9_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_9_2 y z w b u))+((d2_3_3 y z w b u)*(d3_9_1 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_8_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_8_3 y z w b u))+((d2_4_2 y z w b u)*(d3_8_2 y z w b u))))+((((d2_5_0 y z w b u)*(d3_7_4 y z w b u))+((d2_5_1 y z w b u)*(d3_7_3 y z w b u)))+((d2_6_0 y z w b u)*(d3_6_4 y z w b u)))))))))+((-1)*(d4_12_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_4,d0_11_3,d0_11_4,d0_12_3,d0_12_4,d0_9_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_1,d3_10_2,d3_10_3,d3_10_4,d3_11_1,d3_11_2,d3_11_3,d3_11_4,d3_12_1,d3_12_2,d3_12_3,d3_12_4,d3_6_4,d3_7_3,d3_7_4,d3_8_2,d3_8_3,d3_8_4,d3_9_1,d3_9_2,d3_9_3,d3_9_4,d4_12_4]
  ring
#print axioms coefficient_12_4
compact_certificate_declaration theorem coefficient_12_5 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[5]?=some 0 := by
  change some (((((((d0_9_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_10_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_11_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_11_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_12_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_12_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_12_5 y z w b u))+(((d2_0_1 y z w b u)*(d3_12_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_12_3 y z w b u))+((d2_0_3 y z w b u)*(d3_12_2 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_11_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_11_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_11_3 y z w b u))+((d2_1_3 y z w b u)*(d3_11_2 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_10_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_10_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_10_3 y z w b u))+((d2_2_3 y z w b u)*(d3_10_2 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_9_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_9_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_9_3 y z w b u))+((d2_3_3 y z w b u)*(d3_9_2 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_8_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_8_4 y z w b u))+((d2_4_2 y z w b u)*(d3_8_3 y z w b u))))+((((d2_5_0 y z w b u)*(d3_7_5 y z w b u))+((d2_5_1 y z w b u)*(d3_7_4 y z w b u)))+((d2_6_0 y z w b u)*(d3_6_5 y z w b u)))))))))+((-1)*(d4_12_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_5,d0_11_4,d0_11_5,d0_12_4,d0_12_5,d0_9_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_2,d3_10_3,d3_10_4,d3_10_5,d3_11_2,d3_11_3,d3_11_4,d3_11_5,d3_12_2,d3_12_3,d3_12_4,d3_12_5,d3_6_5,d3_7_4,d3_7_5,d3_8_3,d3_8_4,d3_8_5,d3_9_2,d3_9_3,d3_9_4,d3_9_5,d4_12_5]
  ring
#print axioms coefficient_12_5

compact_certificate_declaration theorem coefficient_12_6 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[6]?=some 0 := by
  change some (((((((d0_9_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_10_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_11_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_11_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_12_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_12_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_12_5 y z w b u))+(((d2_0_2 y z w b u)*(d3_12_4 y z w b u))+((d2_0_3 y z w b u)*(d3_12_3 y z w b u))))+((((d2_1_0 y z w b u)*(d3_11_6 y z w b u))+(((d2_1_1 y z w b u)*(d3_11_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_11_4 y z w b u))+((d2_1_3 y z w b u)*(d3_11_3 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_10_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_10_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_10_4 y z w b u))+((d2_2_3 y z w b u)*(d3_10_3 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_9_6 y z w b u))+(((d2_3_1 y z w b u)*(d3_9_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_9_4 y z w b u))+((d2_3_3 y z w b u)*(d3_9_3 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_8_6 y z w b u))+(((d2_4_1 y z w b u)*(d3_8_5 y z w b u))+((d2_4_2 y z w b u)*(d3_8_4 y z w b u))))+((((d2_5_0 y z w b u)*(d3_7_6 y z w b u))+((d2_5_1 y z w b u)*(d3_7_5 y z w b u)))+((d2_6_0 y z w b u)*(d3_6_6 y z w b u)))))))))+((-1)*(d4_12_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_6,d0_11_5,d0_11_6,d0_12_5,d0_12_6,d0_9_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_3,d3_10_4,d3_10_5,d3_10_6,d3_11_3,d3_11_4,d3_11_5,d3_11_6,d3_12_3,d3_12_4,d3_12_5,d3_6_6,d3_7_5,d3_7_6,d3_8_4,d3_8_5,d3_8_6,d3_9_3,d3_9_4,d3_9_5,d3_9_6,d4_12_6]
  ring
#print axioms coefficient_12_6
compact_certificate_declaration theorem coefficient_12_7 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[7]?=some 0 := by
  change some (((((((d0_9_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_10_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_11_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_11_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_12_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_12_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_12_5 y z w b u))+((d2_0_3 y z w b u)*(d3_12_4 y z w b u)))+((((d2_1_1 y z w b u)*(d3_11_6 y z w b u))+(((d2_1_2 y z w b u)*(d3_11_5 y z w b u))+((d2_1_3 y z w b u)*(d3_11_4 y z w b u))))+((((d2_2_1 y z w b u)*(d3_10_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_10_5 y z w b u))+((d2_2_3 y z w b u)*(d3_10_4 y z w b u))))+((((d2_3_0 y z w b u)*(d3_9_7 y z w b u))+(((d2_3_1 y z w b u)*(d3_9_6 y z w b u))+(((d2_3_2 y z w b u)*(d3_9_5 y z w b u))+((d2_3_3 y z w b u)*(d3_9_4 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_8_7 y z w b u))+(((d2_4_1 y z w b u)*(d3_8_6 y z w b u))+((d2_4_2 y z w b u)*(d3_8_5 y z w b u))))+((((d2_5_0 y z w b u)*(d3_7_7 y z w b u))+((d2_5_1 y z w b u)*(d3_7_6 y z w b u)))+((d2_6_0 y z w b u)*(d3_6_7 y z w b u)))))))))+((-1)*(d4_12_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_7,d0_11_6,d0_11_7,d0_12_6,d0_12_7,d0_9_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_1_1,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_4,d3_10_5,d3_10_6,d3_11_4,d3_11_5,d3_11_6,d3_12_4,d3_12_5,d3_6_7,d3_7_6,d3_7_7,d3_8_5,d3_8_6,d3_8_7,d3_9_4,d3_9_5,d3_9_6,d3_9_7,d4_12_7]
  ring
#print axioms coefficient_12_7
compact_certificate_declaration theorem coefficient_12_8 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[8]?=some 0 := by
  change some (((((((d0_9_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_10_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_11_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_11_8 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_12_7 y z w b u)*(d1_0_1 y z w b u))+(((d0_12_8 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_0_3 y z w b u)*(d3_12_5 y z w b u))+((((d2_1_2 y z w b u)*(d3_11_6 y z w b u))+((d2_1_3 y z w b u)*(d3_11_5 y z w b u)))+((((d2_2_2 y z w b u)*(d3_10_6 y z w b u))+((d2_2_3 y z w b u)*(d3_10_5 y z w b u)))+((((d2_3_1 y z w b u)*(d3_9_7 y z w b u))+(((d2_3_2 y z w b u)*(d3_9_6 y z w b u))+((d2_3_3 y z w b u)*(d3_9_5 y z w b u))))+((((d2_4_1 y z w b u)*(d3_8_7 y z w b u))+((d2_4_2 y z w b u)*(d3_8_6 y z w b u)))+(((d2_5_1 y z w b u)*(d3_7_7 y z w b u))+((d2_6_0 y z w b u)*(d3_6_8 y z w b u)))))))))+((-1)*(d4_12_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_8,d0_11_7,d0_11_8,d0_12_7,d0_12_8,d0_9_8,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_1_2,d2_1_3,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d2_5_1,d2_6_0,d3_10_5,d3_10_6,d3_11_5,d3_11_6,d3_12_5,d3_6_8,d3_7_7,d3_8_6,d3_8_7,d3_9_5,d3_9_6,d3_9_7,d4_12_8]
  ring
#print axioms coefficient_12_8

compact_certificate_declaration theorem coefficient_12_9 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[9]?=some 0 := by
  change some ((((((d0_9_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_10_9 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_11_8 y z w b u)*(d1_1_1 y z w b u))+(((d0_11_9 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_12_8 y z w b u)*(d1_0_1 y z w b u)))))+(((d2_1_3 y z w b u)*(d3_11_6 y z w b u))+(((d2_2_3 y z w b u)*(d3_10_6 y z w b u))+((((d2_3_2 y z w b u)*(d3_9_7 y z w b u))+((d2_3_3 y z w b u)*(d3_9_6 y z w b u)))+((d2_4_2 y z w b u)*(d3_8_7 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_9,d0_11_8,d0_11_9,d0_12_8,d0_9_9,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_1_3,d2_2_3,d2_3_2,d2_3_3,d2_4_2,d3_10_6,d3_11_6,d3_8_7,d3_9_6,d3_9_7]
  ring
#print axioms coefficient_12_9
compact_certificate_declaration theorem coefficient_12_10 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[10]?=some 0 := by
  change some ((((d0_11_9 y z w b u)*(d1_1_1 y z w b u))+((d2_3_3 y z w b u)*(d3_9_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_11_9,d1_1_1,d2_3_3,d3_9_7]
  ring
#print axioms coefficient_12_10

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_13 (y z w b u : ℂ) : (innerCertificate13 y z w b u).length=10 := by
  norm_num [innerCertificate13,add,multiply,scale,inner0_10,inner0_11,inner0_12,inner0_13,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_10,inner3_11,inner3_12,inner3_13,inner3_7,inner3_8,inner3_9,inner4_13]
compact_certificate_declaration theorem inner_eval_13 (y z w a b u : ℂ) :
    evaluate a (innerCertificate13 y z w b u)=(((((c0_10 y z w a b u)*(c1_3 y z w a b u))+(((c0_11 y z w a b u)*(c1_2 y z w a b u))+(((c0_12 y z w a b u)*(c1_1 y z w a b u))+(((c0_13 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_13 y z w a b u))+(((c2_1 y z w a b u)*(c3_12 y z w a b u))+(((c2_2 y z w a b u)*(c3_11 y z w a b u))+(((c2_3 y z w a b u)*(c3_10 y z w a b u))+(((c2_4 y z w a b u)*(c3_9 y z w a b u))+(((c2_5 y z w a b u)*(c3_8 y z w a b u))+((c2_6 y z w a b u)*(c3_7 y z w a b u)))))))))+((-1)*(c4_13 y z w a b u))) := by
  simp only [innerCertificate13,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_10,c0_11,c0_12,c0_13,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c3_10,c3_11,c3_12,c3_13,c3_7,c3_8,c3_9,c4_13]
#print axioms inner_eval_13

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_13_0 (y z w b u : ℂ) :
    (innerCertificate13 y z w b u)[0]?=some 0 := by
  change some (((((((d0_10_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_11_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_12_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_13_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_13_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_12_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_11_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_10_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_9_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_8_0 y z w b u))+0)+(((d2_6_0 y z w b u)*(d3_7_0 y z w b u))+0))))))))+(((-1)*(d4_13_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_11_0,d0_12_0,d0_13_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d3_10_0,d3_11_0,d3_12_0,d3_13_0,d3_7_0,d3_8_0,d3_9_0,d4_13_0]
  ring
#print axioms coefficient_13_0
compact_certificate_declaration theorem coefficient_13_1 (y z w b u : ℂ) :
    (innerCertificate13 y z w b u)[1]?=some 0 := by
  change some (((((((d0_10_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_11_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_12_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_12_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_13_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_13_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_13_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_13_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_12_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_12_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_11_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_11_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_10_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_10_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_9_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_9_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_8_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_8_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_7_1 y z w b u)))))))))+((-1)*(d4_13_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_1,d0_11_1,d0_12_0,d0_12_1,d0_13_0,d0_13_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d3_10_0,d3_10_1,d3_11_0,d3_11_1,d3_12_0,d3_12_1,d3_13_0,d3_13_1,d3_7_1,d3_8_0,d3_8_1,d3_9_0,d3_9_1,d4_13_1]
  ring
#print axioms coefficient_13_1
compact_certificate_declaration theorem coefficient_13_2 (y z w b u : ℂ) :
    (innerCertificate13 y z w b u)[2]?=some 0 := by
  change some (((((((d0_10_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_11_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_12_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_12_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_13_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_13_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_13_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_13_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_13_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_12_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_12_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_12_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_11_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_11_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_11_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_10_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_10_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_10_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_9_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_9_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_9_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_8_2 y z w b u))+((d2_5_1 y z w b u)*(d3_8_1 y z w b u)))+((d2_6_0 y z w b u)*(d3_7_2 y z w b u)))))))))+((-1)*(d4_13_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_2,d0_11_2,d0_12_1,d0_12_2,d0_13_1,d0_13_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_0,d3_10_1,d3_10_2,d3_11_0,d3_11_1,d3_11_2,d3_12_0,d3_12_1,d3_12_2,d3_13_0,d3_13_1,d3_13_2,d3_7_2,d3_8_1,d3_8_2,d3_9_0,d3_9_1,d3_9_2,d4_13_2]
  ring
#print axioms coefficient_13_2

compact_certificate_declaration theorem coefficient_13_3 (y z w b u : ℂ) :
    (innerCertificate13 y z w b u)[3]?=some 0 := by
  change some (((((((d0_10_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_11_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_12_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_12_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_13_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_13_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_13_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_13_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_13_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_13_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_12_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_12_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_12_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_12_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_11_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_11_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_11_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_11_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_10_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_10_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_10_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_10_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_9_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_9_2 y z w b u))+((d2_4_2 y z w b u)*(d3_9_1 y z w b u))))+((((d2_5_0 y z w b u)*(d3_8_3 y z w b u))+((d2_5_1 y z w b u)*(d3_8_2 y z w b u)))+((d2_6_0 y z w b u)*(d3_7_3 y z w b u)))))))))+((-1)*(d4_13_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_3,d0_11_3,d0_12_2,d0_12_3,d0_13_2,d0_13_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_0,d3_10_1,d3_10_2,d3_10_3,d3_11_0,d3_11_1,d3_11_2,d3_11_3,d3_12_0,d3_12_1,d3_12_2,d3_12_3,d3_13_0,d3_13_1,d3_13_2,d3_13_3,d3_7_3,d3_8_2,d3_8_3,d3_9_1,d3_9_2,d3_9_3,d4_13_3]
  ring
#print axioms coefficient_13_3
compact_certificate_declaration theorem coefficient_13_4 (y z w b u : ℂ) :
    (innerCertificate13 y z w b u)[4]?=some 0 := by
  change some (((((((d0_10_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_11_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_12_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_12_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_13_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_13_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_13_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_13_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_13_2 y z w b u))+((d2_0_3 y z w b u)*(d3_13_1 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_12_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_12_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_12_2 y z w b u))+((d2_1_3 y z w b u)*(d3_12_1 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_11_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_11_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_11_2 y z w b u))+((d2_2_3 y z w b u)*(d3_11_1 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_10_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_10_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_10_2 y z w b u))+((d2_3_3 y z w b u)*(d3_10_1 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_9_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_9_3 y z w b u))+((d2_4_2 y z w b u)*(d3_9_2 y z w b u))))+((((d2_5_0 y z w b u)*(d3_8_4 y z w b u))+((d2_5_1 y z w b u)*(d3_8_3 y z w b u)))+((d2_6_0 y z w b u)*(d3_7_4 y z w b u)))))))))+((-1)*(d4_13_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_4,d0_11_4,d0_12_3,d0_12_4,d0_13_3,d0_13_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_1,d3_10_2,d3_10_3,d3_10_4,d3_11_1,d3_11_2,d3_11_3,d3_11_4,d3_12_1,d3_12_2,d3_12_3,d3_12_4,d3_13_1,d3_13_2,d3_13_3,d3_13_4,d3_7_4,d3_8_3,d3_8_4,d3_9_2,d3_9_3,d3_9_4,d4_13_4]
  ring
#print axioms coefficient_13_4
compact_certificate_declaration theorem coefficient_13_5 (y z w b u : ℂ) :
    (innerCertificate13 y z w b u)[5]?=some 0 := by
  change some (((((((d0_10_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_11_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_12_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_12_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_13_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_13_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_13_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_13_3 y z w b u))+((d2_0_3 y z w b u)*(d3_13_2 y z w b u))))+((((d2_1_0 y z w b u)*(d3_12_5 y z w b u))+(((d2_1_1 y z w b u)*(d3_12_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_12_3 y z w b u))+((d2_1_3 y z w b u)*(d3_12_2 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_11_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_11_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_11_3 y z w b u))+((d2_2_3 y z w b u)*(d3_11_2 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_10_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_10_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_10_3 y z w b u))+((d2_3_3 y z w b u)*(d3_10_2 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_9_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_9_4 y z w b u))+((d2_4_2 y z w b u)*(d3_9_3 y z w b u))))+((((d2_5_0 y z w b u)*(d3_8_5 y z w b u))+((d2_5_1 y z w b u)*(d3_8_4 y z w b u)))+((d2_6_0 y z w b u)*(d3_7_5 y z w b u)))))))))+((-1)*(d4_13_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_5,d0_11_5,d0_12_4,d0_12_5,d0_13_4,d0_13_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_2,d3_10_3,d3_10_4,d3_10_5,d3_11_2,d3_11_3,d3_11_4,d3_11_5,d3_12_2,d3_12_3,d3_12_4,d3_12_5,d3_13_2,d3_13_3,d3_13_4,d3_7_5,d3_8_4,d3_8_5,d3_9_3,d3_9_4,d3_9_5,d4_13_5]
  ring
#print axioms coefficient_13_5

compact_certificate_declaration theorem coefficient_13_6 (y z w b u : ℂ) :
    (innerCertificate13 y z w b u)[6]?=some 0 := by
  change some (((((((d0_10_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_11_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_12_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_12_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_13_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_13_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_13_4 y z w b u))+((d2_0_3 y z w b u)*(d3_13_3 y z w b u)))+((((d2_1_1 y z w b u)*(d3_12_5 y z w b u))+(((d2_1_2 y z w b u)*(d3_12_4 y z w b u))+((d2_1_3 y z w b u)*(d3_12_3 y z w b u))))+((((d2_2_0 y z w b u)*(d3_11_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_11_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_11_4 y z w b u))+((d2_2_3 y z w b u)*(d3_11_3 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_10_6 y z w b u))+(((d2_3_1 y z w b u)*(d3_10_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_10_4 y z w b u))+((d2_3_3 y z w b u)*(d3_10_3 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_9_6 y z w b u))+(((d2_4_1 y z w b u)*(d3_9_5 y z w b u))+((d2_4_2 y z w b u)*(d3_9_4 y z w b u))))+((((d2_5_0 y z w b u)*(d3_8_6 y z w b u))+((d2_5_1 y z w b u)*(d3_8_5 y z w b u)))+((d2_6_0 y z w b u)*(d3_7_6 y z w b u)))))))))+((-1)*(d4_13_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_6,d0_11_6,d0_12_5,d0_12_6,d0_13_5,d0_13_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_3,d3_10_4,d3_10_5,d3_10_6,d3_11_3,d3_11_4,d3_11_5,d3_11_6,d3_12_3,d3_12_4,d3_12_5,d3_13_3,d3_13_4,d3_7_6,d3_8_5,d3_8_6,d3_9_4,d3_9_5,d3_9_6,d4_13_6]
  ring
#print axioms coefficient_13_6
compact_certificate_declaration theorem coefficient_13_7 (y z w b u : ℂ) :
    (innerCertificate13 y z w b u)[7]?=some 0 := by
  change some (((((((d0_10_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_11_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_12_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_12_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_13_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_13_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_0_3 y z w b u)*(d3_13_4 y z w b u))+((((d2_1_2 y z w b u)*(d3_12_5 y z w b u))+((d2_1_3 y z w b u)*(d3_12_4 y z w b u)))+((((d2_2_1 y z w b u)*(d3_11_6 y z w b u))+(((d2_2_2 y z w b u)*(d3_11_5 y z w b u))+((d2_2_3 y z w b u)*(d3_11_4 y z w b u))))+((((d2_3_1 y z w b u)*(d3_10_6 y z w b u))+(((d2_3_2 y z w b u)*(d3_10_5 y z w b u))+((d2_3_3 y z w b u)*(d3_10_4 y z w b u))))+((((d2_4_0 y z w b u)*(d3_9_7 y z w b u))+(((d2_4_1 y z w b u)*(d3_9_6 y z w b u))+((d2_4_2 y z w b u)*(d3_9_5 y z w b u))))+((((d2_5_0 y z w b u)*(d3_8_7 y z w b u))+((d2_5_1 y z w b u)*(d3_8_6 y z w b u)))+((d2_6_0 y z w b u)*(d3_7_7 y z w b u)))))))))+((-1)*(d4_13_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_7,d0_11_7,d0_12_6,d0_12_7,d0_13_6,d0_13_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_4,d3_10_5,d3_10_6,d3_11_4,d3_11_5,d3_11_6,d3_12_4,d3_12_5,d3_13_4,d3_7_7,d3_8_6,d3_8_7,d3_9_5,d3_9_6,d3_9_7,d4_13_7]
  ring
#print axioms coefficient_13_7
compact_certificate_declaration theorem coefficient_13_8 (y z w b u : ℂ) :
    (innerCertificate13 y z w b u)[8]?=some 0 := by
  change some (((((((d0_10_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_11_8 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_12_7 y z w b u)*(d1_1_1 y z w b u))+(((d0_12_8 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_13_7 y z w b u)*(d1_0_1 y z w b u)))))+(((d2_1_3 y z w b u)*(d3_12_5 y z w b u))+((((d2_2_2 y z w b u)*(d3_11_6 y z w b u))+((d2_2_3 y z w b u)*(d3_11_5 y z w b u)))+((((d2_3_2 y z w b u)*(d3_10_6 y z w b u))+((d2_3_3 y z w b u)*(d3_10_5 y z w b u)))+((((d2_4_1 y z w b u)*(d3_9_7 y z w b u))+((d2_4_2 y z w b u)*(d3_9_6 y z w b u)))+((d2_5_1 y z w b u)*(d3_8_7 y z w b u)))))))+((-1)*(d4_13_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_8,d0_11_8,d0_12_7,d0_12_8,d0_13_7,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_1_3,d2_2_2,d2_2_3,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d2_5_1,d3_10_5,d3_10_6,d3_11_5,d3_11_6,d3_12_5,d3_8_7,d3_9_6,d3_9_7,d4_13_8]
  ring
#print axioms coefficient_13_8

compact_certificate_declaration theorem coefficient_13_9 (y z w b u : ℂ) :
    (innerCertificate13 y z w b u)[9]?=some 0 := by
  change some ((((((d0_10_9 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_11_9 y z w b u)*(d1_2_0 y z w b u))+0)+((d0_12_8 y z w b u)*(d1_1_1 y z w b u))))+(((d2_2_3 y z w b u)*(d3_11_6 y z w b u))+(((d2_3_3 y z w b u)*(d3_10_6 y z w b u))+((d2_4_2 y z w b u)*(d3_9_7 y z w b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_9,d0_11_9,d0_12_8,d1_1_1,d1_2_0,d1_3_0,d2_2_3,d2_3_3,d2_4_2,d3_10_6,d3_11_6,d3_9_7]
  ring
#print axioms coefficient_13_9

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_14 (y z w b u : ℂ) : (innerCertificate14 y z w b u).length=10 := by
  norm_num [innerCertificate14,add,multiply,scale,inner0_11,inner0_12,inner0_13,inner0_14,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_8,inner3_9,inner4_14]
compact_certificate_declaration theorem inner_eval_14 (y z w a b u : ℂ) :
    evaluate a (innerCertificate14 y z w b u)=(((((c0_11 y z w a b u)*(c1_3 y z w a b u))+(((c0_12 y z w a b u)*(c1_2 y z w a b u))+(((c0_13 y z w a b u)*(c1_1 y z w a b u))+(((c0_14 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_14 y z w a b u))+(((c2_1 y z w a b u)*(c3_13 y z w a b u))+(((c2_2 y z w a b u)*(c3_12 y z w a b u))+(((c2_3 y z w a b u)*(c3_11 y z w a b u))+(((c2_4 y z w a b u)*(c3_10 y z w a b u))+(((c2_5 y z w a b u)*(c3_9 y z w a b u))+((c2_6 y z w a b u)*(c3_8 y z w a b u)))))))))+((-1)*(c4_14 y z w a b u))) := by
  simp only [innerCertificate14,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_11,c0_12,c0_13,c0_14,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c3_10,c3_11,c3_12,c3_13,c3_14,c3_8,c3_9,c4_14]
#print axioms inner_eval_14

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_14_0 (y z w b u : ℂ) :
    (innerCertificate14 y z w b u)[0]?=some 0 := by
  change some (((((((d0_11_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_12_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_13_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_14_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_14_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_13_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_12_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_11_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_10_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_9_0 y z w b u))+0)+(((d2_6_0 y z w b u)*(d3_8_0 y z w b u))+0))))))))+(((-1)*(d4_14_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_11_0,d0_12_0,d0_13_0,d0_14_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d3_10_0,d3_11_0,d3_12_0,d3_13_0,d3_14_0,d3_8_0,d3_9_0,d4_14_0]
  ring
#print axioms coefficient_14_0
compact_certificate_declaration theorem coefficient_14_1 (y z w b u : ℂ) :
    (innerCertificate14 y z w b u)[1]?=some 0 := by
  change some (((((((d0_11_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_12_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_13_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_13_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_14_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_14_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_14_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_14_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_13_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_13_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_12_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_12_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_11_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_11_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_10_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_10_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_9_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_9_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_8_1 y z w b u)))))))))+((-1)*(d4_14_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_11_1,d0_12_1,d0_13_0,d0_13_1,d0_14_0,d0_14_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d3_10_0,d3_10_1,d3_11_0,d3_11_1,d3_12_0,d3_12_1,d3_13_0,d3_13_1,d3_14_0,d3_14_1,d3_8_1,d3_9_0,d3_9_1,d4_14_1]
  ring
#print axioms coefficient_14_1
compact_certificate_declaration theorem coefficient_14_2 (y z w b u : ℂ) :
    (innerCertificate14 y z w b u)[2]?=some 0 := by
  change some (((((((d0_11_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_12_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_13_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_13_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_14_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_14_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_14_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_14_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_14_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_13_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_13_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_13_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_12_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_12_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_12_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_11_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_11_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_11_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_10_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_10_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_10_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_9_2 y z w b u))+((d2_5_1 y z w b u)*(d3_9_1 y z w b u)))+((d2_6_0 y z w b u)*(d3_8_2 y z w b u)))))))))+((-1)*(d4_14_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_11_2,d0_12_2,d0_13_1,d0_13_2,d0_14_1,d0_14_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_0,d3_10_1,d3_10_2,d3_11_0,d3_11_1,d3_11_2,d3_12_0,d3_12_1,d3_12_2,d3_13_0,d3_13_1,d3_13_2,d3_14_0,d3_14_1,d3_14_2,d3_8_2,d3_9_1,d3_9_2,d4_14_2]
  ring
#print axioms coefficient_14_2

compact_certificate_declaration theorem coefficient_14_3 (y z w b u : ℂ) :
    (innerCertificate14 y z w b u)[3]?=some 0 := by
  change some (((((((d0_11_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_12_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_13_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_13_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_14_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_14_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_14_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_14_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_14_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_14_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_13_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_13_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_13_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_13_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_12_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_12_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_12_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_12_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_11_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_11_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_11_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_11_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_10_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_10_2 y z w b u))+((d2_4_2 y z w b u)*(d3_10_1 y z w b u))))+((((d2_5_0 y z w b u)*(d3_9_3 y z w b u))+((d2_5_1 y z w b u)*(d3_9_2 y z w b u)))+((d2_6_0 y z w b u)*(d3_8_3 y z w b u)))))))))+((-1)*(d4_14_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_11_3,d0_12_3,d0_13_2,d0_13_3,d0_14_2,d0_14_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_1,d3_10_2,d3_10_3,d3_11_0,d3_11_1,d3_11_2,d3_11_3,d3_12_0,d3_12_1,d3_12_2,d3_12_3,d3_13_0,d3_13_1,d3_13_2,d3_13_3,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_8_3,d3_9_2,d3_9_3,d4_14_3]
  ring
#print axioms coefficient_14_3
compact_certificate_declaration theorem coefficient_14_4 (y z w b u : ℂ) :
    (innerCertificate14 y z w b u)[4]?=some 0 := by
  change some (((((((d0_11_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_12_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_13_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_13_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_14_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_14_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_14_4 y z w b u))+(((d2_0_1 y z w b u)*(d3_14_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_14_2 y z w b u))+((d2_0_3 y z w b u)*(d3_14_1 y z w b u)))))+((((d2_1_0 y z w b u)*(d3_13_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_13_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_13_2 y z w b u))+((d2_1_3 y z w b u)*(d3_13_1 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_12_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_12_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_12_2 y z w b u))+((d2_2_3 y z w b u)*(d3_12_1 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_11_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_11_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_11_2 y z w b u))+((d2_3_3 y z w b u)*(d3_11_1 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_10_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_10_3 y z w b u))+((d2_4_2 y z w b u)*(d3_10_2 y z w b u))))+((((d2_5_0 y z w b u)*(d3_9_4 y z w b u))+((d2_5_1 y z w b u)*(d3_9_3 y z w b u)))+((d2_6_0 y z w b u)*(d3_8_4 y z w b u)))))))))+((-1)*(d4_14_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_11_4,d0_12_4,d0_13_3,d0_13_4,d0_14_3,d0_14_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_2,d3_10_3,d3_10_4,d3_11_1,d3_11_2,d3_11_3,d3_11_4,d3_12_1,d3_12_2,d3_12_3,d3_12_4,d3_13_1,d3_13_2,d3_13_3,d3_13_4,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_8_4,d3_9_3,d3_9_4,d4_14_4]
  ring
#print axioms coefficient_14_4
compact_certificate_declaration theorem coefficient_14_5 (y z w b u : ℂ) :
    (innerCertificate14 y z w b u)[5]?=some 0 := by
  change some (((((((d0_11_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_12_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_13_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_13_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_14_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_14_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_14_4 y z w b u))+(((d2_0_2 y z w b u)*(d3_14_3 y z w b u))+((d2_0_3 y z w b u)*(d3_14_2 y z w b u))))+((((d2_1_1 y z w b u)*(d3_13_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_13_3 y z w b u))+((d2_1_3 y z w b u)*(d3_13_2 y z w b u))))+((((d2_2_0 y z w b u)*(d3_12_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_12_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_12_3 y z w b u))+((d2_2_3 y z w b u)*(d3_12_2 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_11_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_11_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_11_3 y z w b u))+((d2_3_3 y z w b u)*(d3_11_2 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_10_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_10_4 y z w b u))+((d2_4_2 y z w b u)*(d3_10_3 y z w b u))))+((((d2_5_0 y z w b u)*(d3_9_5 y z w b u))+((d2_5_1 y z w b u)*(d3_9_4 y z w b u)))+((d2_6_0 y z w b u)*(d3_8_5 y z w b u)))))))))+((-1)*(d4_14_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_11_5,d0_12_5,d0_13_4,d0_13_5,d0_14_4,d0_14_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_3,d3_10_4,d3_10_5,d3_11_2,d3_11_3,d3_11_4,d3_11_5,d3_12_2,d3_12_3,d3_12_4,d3_12_5,d3_13_2,d3_13_3,d3_13_4,d3_14_2,d3_14_3,d3_14_4,d3_8_5,d3_9_4,d3_9_5,d4_14_5]
  ring
#print axioms coefficient_14_5

compact_certificate_declaration theorem coefficient_14_6 (y z w b u : ℂ) :
    (innerCertificate14 y z w b u)[6]?=some 0 := by
  change some (((((((d0_11_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_12_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_13_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_13_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_14_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_14_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_14_4 y z w b u))+((d2_0_3 y z w b u)*(d3_14_3 y z w b u)))+((((d2_1_2 y z w b u)*(d3_13_4 y z w b u))+((d2_1_3 y z w b u)*(d3_13_3 y z w b u)))+((((d2_2_1 y z w b u)*(d3_12_5 y z w b u))+(((d2_2_2 y z w b u)*(d3_12_4 y z w b u))+((d2_2_3 y z w b u)*(d3_12_3 y z w b u))))+((((d2_3_0 y z w b u)*(d3_11_6 y z w b u))+(((d2_3_1 y z w b u)*(d3_11_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_11_4 y z w b u))+((d2_3_3 y z w b u)*(d3_11_3 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_10_6 y z w b u))+(((d2_4_1 y z w b u)*(d3_10_5 y z w b u))+((d2_4_2 y z w b u)*(d3_10_4 y z w b u))))+((((d2_5_0 y z w b u)*(d3_9_6 y z w b u))+((d2_5_1 y z w b u)*(d3_9_5 y z w b u)))+((d2_6_0 y z w b u)*(d3_8_6 y z w b u)))))))))+((-1)*(d4_14_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_11_6,d0_12_6,d0_13_5,d0_13_6,d0_14_5,d0_14_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_4,d3_10_5,d3_10_6,d3_11_3,d3_11_4,d3_11_5,d3_11_6,d3_12_3,d3_12_4,d3_12_5,d3_13_3,d3_13_4,d3_14_3,d3_14_4,d3_8_6,d3_9_5,d3_9_6,d4_14_6]
  ring
#print axioms coefficient_14_6
compact_certificate_declaration theorem coefficient_14_7 (y z w b u : ℂ) :
    (innerCertificate14 y z w b u)[7]?=some 0 := by
  change some (((((((d0_11_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_12_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_13_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_13_7 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_14_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_14_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_0_3 y z w b u)*(d3_14_4 y z w b u))+(((d2_1_3 y z w b u)*(d3_13_4 y z w b u))+((((d2_2_2 y z w b u)*(d3_12_5 y z w b u))+((d2_2_3 y z w b u)*(d3_12_4 y z w b u)))+((((d2_3_1 y z w b u)*(d3_11_6 y z w b u))+(((d2_3_2 y z w b u)*(d3_11_5 y z w b u))+((d2_3_3 y z w b u)*(d3_11_4 y z w b u))))+((((d2_4_1 y z w b u)*(d3_10_6 y z w b u))+((d2_4_2 y z w b u)*(d3_10_5 y z w b u)))+((((d2_5_0 y z w b u)*(d3_9_7 y z w b u))+((d2_5_1 y z w b u)*(d3_9_6 y z w b u)))+((d2_6_0 y z w b u)*(d3_8_7 y z w b u)))))))))+((-1)*(d4_14_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_11_7,d0_12_7,d0_13_6,d0_13_7,d0_14_6,d0_14_7,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_1_3,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_5,d3_10_6,d3_11_4,d3_11_5,d3_11_6,d3_12_4,d3_12_5,d3_13_4,d3_14_4,d3_8_7,d3_9_6,d3_9_7,d4_14_7]
  ring
#print axioms coefficient_14_7
compact_certificate_declaration theorem coefficient_14_8 (y z w b u : ℂ) :
    (innerCertificate14 y z w b u)[8]?=some 0 := by
  change some ((((((d0_11_8 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_12_8 y z w b u)*(d1_2_0 y z w b u))+0)+(((d0_13_7 y z w b u)*(d1_1_1 y z w b u))+((d0_14_7 y z w b u)*(d1_0_1 y z w b u)))))+(((d2_2_3 y z w b u)*(d3_12_5 y z w b u))+((((d2_3_2 y z w b u)*(d3_11_6 y z w b u))+((d2_3_3 y z w b u)*(d3_11_5 y z w b u)))+(((d2_4_2 y z w b u)*(d3_10_6 y z w b u))+((d2_5_1 y z w b u)*(d3_9_7 y z w b u)))))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_11_8,d0_12_8,d0_13_7,d0_14_7,d1_0_1,d1_1_1,d1_2_0,d1_3_0,d2_2_3,d2_3_2,d2_3_3,d2_4_2,d2_5_1,d3_10_6,d3_11_5,d3_11_6,d3_12_5,d3_9_7]
  ring
#print axioms coefficient_14_8

compact_certificate_declaration theorem coefficient_14_9 (y z w b u : ℂ) :
    (innerCertificate14 y z w b u)[9]?=some 0 := by
  change some (((((d0_11_9 y z w b u)*(d1_3_0 y z w b u))+0)+((d2_3_3 y z w b u)*(d3_11_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_11_9,d1_3_0,d2_3_3,d3_11_6]
  ring
#print axioms coefficient_14_9

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_15 (y z w b u : ℂ) : (innerCertificate15 y z w b u).length=9 := by
  norm_num [innerCertificate15,add,multiply,scale,inner0_12,inner0_13,inner0_14,inner0_15,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_9,inner4_15]
compact_certificate_declaration theorem inner_eval_15 (y z w a b u : ℂ) :
    evaluate a (innerCertificate15 y z w b u)=(((((c0_12 y z w a b u)*(c1_3 y z w a b u))+(((c0_13 y z w a b u)*(c1_2 y z w a b u))+(((c0_14 y z w a b u)*(c1_1 y z w a b u))+(((c0_15 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_15 y z w a b u))+(((c2_1 y z w a b u)*(c3_14 y z w a b u))+(((c2_2 y z w a b u)*(c3_13 y z w a b u))+(((c2_3 y z w a b u)*(c3_12 y z w a b u))+(((c2_4 y z w a b u)*(c3_11 y z w a b u))+(((c2_5 y z w a b u)*(c3_10 y z w a b u))+((c2_6 y z w a b u)*(c3_9 y z w a b u)))))))))+((-1)*(c4_15 y z w a b u))) := by
  simp only [innerCertificate15,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_12,c0_13,c0_14,c0_15,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_9,c4_15]
#print axioms inner_eval_15

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_15_0 (y z w b u : ℂ) :
    (innerCertificate15 y z w b u)[0]?=some 0 := by
  change some (((((((d0_12_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_13_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_14_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_15_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_15_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_14_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_13_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_12_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_11_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_10_0 y z w b u))+0)+(((d2_6_0 y z w b u)*(d3_9_0 y z w b u))+0))))))))+(((-1)*(d4_15_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_12_0,d0_13_0,d0_14_0,d0_15_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d3_10_0,d3_11_0,d3_12_0,d3_13_0,d3_14_0,d3_15_0,d3_9_0,d4_15_0]
  ring
#print axioms coefficient_15_0
compact_certificate_declaration theorem coefficient_15_1 (y z w b u : ℂ) :
    (innerCertificate15 y z w b u)[1]?=some 0 := by
  change some (((((((d0_12_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_13_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_14_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_14_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_15_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_15_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_15_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_15_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_14_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_14_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_13_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_13_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_12_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_12_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_11_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_11_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_10_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_10_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_9_1 y z w b u)))))))))+((-1)*(d4_15_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_12_1,d0_13_1,d0_14_0,d0_14_1,d0_15_0,d0_15_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d3_10_0,d3_10_1,d3_11_0,d3_11_1,d3_12_0,d3_12_1,d3_13_0,d3_13_1,d3_14_0,d3_14_1,d3_15_0,d3_15_1,d3_9_1,d4_15_1]
  ring
#print axioms coefficient_15_1
compact_certificate_declaration theorem coefficient_15_2 (y z w b u : ℂ) :
    (innerCertificate15 y z w b u)[2]?=some 0 := by
  change some (((((((d0_12_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_13_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_14_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_14_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_15_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_15_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_15_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_15_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_15_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_14_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_14_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_14_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_13_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_13_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_13_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_12_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_12_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_12_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_11_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_11_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_11_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_10_2 y z w b u))+((d2_5_1 y z w b u)*(d3_10_1 y z w b u)))+((d2_6_0 y z w b u)*(d3_9_2 y z w b u)))))))))+((-1)*(d4_15_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_12_2,d0_13_2,d0_14_1,d0_14_2,d0_15_1,d0_15_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_1,d3_10_2,d3_11_0,d3_11_1,d3_11_2,d3_12_0,d3_12_1,d3_12_2,d3_13_0,d3_13_1,d3_13_2,d3_14_0,d3_14_1,d3_14_2,d3_15_0,d3_15_1,d3_15_2,d3_9_2,d4_15_2]
  ring
#print axioms coefficient_15_2

compact_certificate_declaration theorem coefficient_15_3 (y z w b u : ℂ) :
    (innerCertificate15 y z w b u)[3]?=some 0 := by
  change some (((((((d0_12_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_13_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_14_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_14_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_15_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_15_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_15_3 y z w b u))+(((d2_0_1 y z w b u)*(d3_15_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_15_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_15_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_14_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_14_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_14_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_14_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_13_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_13_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_13_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_13_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_12_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_12_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_12_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_12_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_11_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_11_2 y z w b u))+((d2_4_2 y z w b u)*(d3_11_1 y z w b u))))+((((d2_5_0 y z w b u)*(d3_10_3 y z w b u))+((d2_5_1 y z w b u)*(d3_10_2 y z w b u)))+((d2_6_0 y z w b u)*(d3_9_3 y z w b u)))))))))+((-1)*(d4_15_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_12_3,d0_13_3,d0_14_2,d0_14_3,d0_15_2,d0_15_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_2,d3_10_3,d3_11_1,d3_11_2,d3_11_3,d3_12_0,d3_12_1,d3_12_2,d3_12_3,d3_13_0,d3_13_1,d3_13_2,d3_13_3,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_9_3,d4_15_3]
  ring
#print axioms coefficient_15_3
compact_certificate_declaration theorem coefficient_15_4 (y z w b u : ℂ) :
    (innerCertificate15 y z w b u)[4]?=some 0 := by
  change some (((((((d0_12_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_13_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_14_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_14_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_15_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_15_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_15_3 y z w b u))+(((d2_0_2 y z w b u)*(d3_15_2 y z w b u))+((d2_0_3 y z w b u)*(d3_15_1 y z w b u))))+((((d2_1_0 y z w b u)*(d3_14_4 y z w b u))+(((d2_1_1 y z w b u)*(d3_14_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_14_2 y z w b u))+((d2_1_3 y z w b u)*(d3_14_1 y z w b u)))))+((((d2_2_0 y z w b u)*(d3_13_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_13_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_13_2 y z w b u))+((d2_2_3 y z w b u)*(d3_13_1 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_12_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_12_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_12_2 y z w b u))+((d2_3_3 y z w b u)*(d3_12_1 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_11_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_11_3 y z w b u))+((d2_4_2 y z w b u)*(d3_11_2 y z w b u))))+((((d2_5_0 y z w b u)*(d3_10_4 y z w b u))+((d2_5_1 y z w b u)*(d3_10_3 y z w b u)))+((d2_6_0 y z w b u)*(d3_9_4 y z w b u)))))))))+((-1)*(d4_15_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_12_4,d0_13_4,d0_14_3,d0_14_4,d0_15_3,d0_15_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_3,d3_10_4,d3_11_2,d3_11_3,d3_11_4,d3_12_1,d3_12_2,d3_12_3,d3_12_4,d3_13_1,d3_13_2,d3_13_3,d3_13_4,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_1,d3_15_2,d3_15_3,d3_9_4,d4_15_4]
  ring
#print axioms coefficient_15_4
compact_certificate_declaration theorem coefficient_15_5 (y z w b u : ℂ) :
    (innerCertificate15 y z w b u)[5]?=some 0 := by
  change some (((((((d0_12_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_13_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_14_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_14_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_15_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_15_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_15_3 y z w b u))+((d2_0_3 y z w b u)*(d3_15_2 y z w b u)))+((((d2_1_1 y z w b u)*(d3_14_4 y z w b u))+(((d2_1_2 y z w b u)*(d3_14_3 y z w b u))+((d2_1_3 y z w b u)*(d3_14_2 y z w b u))))+((((d2_2_1 y z w b u)*(d3_13_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_13_3 y z w b u))+((d2_2_3 y z w b u)*(d3_13_2 y z w b u))))+((((d2_3_0 y z w b u)*(d3_12_5 y z w b u))+(((d2_3_1 y z w b u)*(d3_12_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_12_3 y z w b u))+((d2_3_3 y z w b u)*(d3_12_2 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_11_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_11_4 y z w b u))+((d2_4_2 y z w b u)*(d3_11_3 y z w b u))))+((((d2_5_0 y z w b u)*(d3_10_5 y z w b u))+((d2_5_1 y z w b u)*(d3_10_4 y z w b u)))+((d2_6_0 y z w b u)*(d3_9_5 y z w b u)))))))))+((-1)*(d4_15_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_12_5,d0_13_5,d0_14_4,d0_14_5,d0_15_4,d0_15_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_1_1,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_4,d3_10_5,d3_11_3,d3_11_4,d3_11_5,d3_12_2,d3_12_3,d3_12_4,d3_12_5,d3_13_2,d3_13_3,d3_13_4,d3_14_2,d3_14_3,d3_14_4,d3_15_2,d3_15_3,d3_9_5,d4_15_5]
  ring
#print axioms coefficient_15_5

compact_certificate_declaration theorem coefficient_15_6 (y z w b u : ℂ) :
    (innerCertificate15 y z w b u)[6]?=some 0 := by
  change some (((((((d0_12_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_13_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_14_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_14_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_15_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_15_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_0_3 y z w b u)*(d3_15_3 y z w b u))+((((d2_1_2 y z w b u)*(d3_14_4 y z w b u))+((d2_1_3 y z w b u)*(d3_14_3 y z w b u)))+((((d2_2_2 y z w b u)*(d3_13_4 y z w b u))+((d2_2_3 y z w b u)*(d3_13_3 y z w b u)))+((((d2_3_1 y z w b u)*(d3_12_5 y z w b u))+(((d2_3_2 y z w b u)*(d3_12_4 y z w b u))+((d2_3_3 y z w b u)*(d3_12_3 y z w b u))))+((((d2_4_0 y z w b u)*(d3_11_6 y z w b u))+(((d2_4_1 y z w b u)*(d3_11_5 y z w b u))+((d2_4_2 y z w b u)*(d3_11_4 y z w b u))))+((((d2_5_0 y z w b u)*(d3_10_6 y z w b u))+((d2_5_1 y z w b u)*(d3_10_5 y z w b u)))+((d2_6_0 y z w b u)*(d3_9_6 y z w b u)))))))))+((-1)*(d4_15_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_12_6,d0_13_6,d0_14_5,d0_14_6,d0_15_5,d0_15_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_1_2,d2_1_3,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_5,d3_10_6,d3_11_4,d3_11_5,d3_11_6,d3_12_3,d3_12_4,d3_12_5,d3_13_3,d3_13_4,d3_14_3,d3_14_4,d3_15_3,d3_9_6,d4_15_6]
  ring
#print axioms coefficient_15_6
compact_certificate_declaration theorem coefficient_15_7 (y z w b u : ℂ) :
    (innerCertificate15 y z w b u)[7]?=some 0 := by
  change some (((((((d0_12_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_13_7 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_14_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_14_7 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_15_6 y z w b u)*(d1_0_1 y z w b u)))))+(((d2_1_3 y z w b u)*(d3_14_4 y z w b u))+(((d2_2_3 y z w b u)*(d3_13_4 y z w b u))+((((d2_3_2 y z w b u)*(d3_12_5 y z w b u))+((d2_3_3 y z w b u)*(d3_12_4 y z w b u)))+((((d2_4_1 y z w b u)*(d3_11_6 y z w b u))+((d2_4_2 y z w b u)*(d3_11_5 y z w b u)))+(((d2_5_1 y z w b u)*(d3_10_6 y z w b u))+((d2_6_0 y z w b u)*(d3_9_7 y z w b u))))))))+((-1)*(d4_15_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_12_7,d0_13_7,d0_14_6,d0_14_7,d0_15_6,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_1_3,d2_2_3,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d2_5_1,d2_6_0,d3_10_6,d3_11_5,d3_11_6,d3_12_4,d3_12_5,d3_13_4,d3_14_4,d3_9_7,d4_15_7]
  ring
#print axioms coefficient_15_7
compact_certificate_declaration theorem coefficient_15_8 (y z w b u : ℂ) :
    (innerCertificate15 y z w b u)[8]?=some 0 := by
  change some ((((((d0_12_8 y z w b u)*(d1_3_0 y z w b u))+0)+((d0_14_7 y z w b u)*(d1_1_1 y z w b u)))+(((d2_3_3 y z w b u)*(d3_12_5 y z w b u))+((d2_4_2 y z w b u)*(d3_11_6 y z w b u)))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_12_8,d0_14_7,d1_1_1,d1_3_0,d2_3_3,d2_4_2,d3_11_6,d3_12_5]
  ring
#print axioms coefficient_15_8

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_16 (y z w b u : ℂ) : (innerCertificate16 y z w b u).length=8 := by
  norm_num [innerCertificate16,add,multiply,scale,inner0_13,inner0_14,inner0_15,inner0_16,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner4_16]
compact_certificate_declaration theorem inner_eval_16 (y z w a b u : ℂ) :
    evaluate a (innerCertificate16 y z w b u)=(((((c0_13 y z w a b u)*(c1_3 y z w a b u))+(((c0_14 y z w a b u)*(c1_2 y z w a b u))+(((c0_15 y z w a b u)*(c1_1 y z w a b u))+(((c0_16 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_16 y z w a b u))+(((c2_1 y z w a b u)*(c3_15 y z w a b u))+(((c2_2 y z w a b u)*(c3_14 y z w a b u))+(((c2_3 y z w a b u)*(c3_13 y z w a b u))+(((c2_4 y z w a b u)*(c3_12 y z w a b u))+(((c2_5 y z w a b u)*(c3_11 y z w a b u))+((c2_6 y z w a b u)*(c3_10 y z w a b u)))))))))+((-1)*(c4_16 y z w a b u))) := by
  simp only [innerCertificate16,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_13,c0_14,c0_15,c0_16,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c4_16]
#print axioms inner_eval_16

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_16_0 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[0]?=some 0 := by
  change some (((((((d0_13_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_16_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_16_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_15_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_14_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_13_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_12_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_11_0 y z w b u))+0)+(((d2_6_0 y z w b u)*(d3_10_0 y z w b u))+0))))))))+(((-1)*(d4_16_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_0,d0_14_0,d0_15_0,d0_16_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d3_10_0,d3_11_0,d3_12_0,d3_13_0,d3_14_0,d3_15_0,d3_16_0,d4_16_0]
  ring
#print axioms coefficient_16_0
compact_certificate_declaration theorem coefficient_16_1 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[1]?=some 0 := by
  change some (((((((d0_13_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_15_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_16_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_16_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_16_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_16_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_15_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_15_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_14_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_14_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_13_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_13_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_12_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_12_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_11_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_11_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_10_1 y z w b u)))))))))+((-1)*(d4_16_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_1,d0_14_1,d0_15_0,d0_15_1,d0_16_0,d0_16_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d3_10_1,d3_11_0,d3_11_1,d3_12_0,d3_12_1,d3_13_0,d3_13_1,d3_14_0,d3_14_1,d3_15_0,d3_15_1,d3_16_0,d3_16_1,d4_16_1]
  ring
#print axioms coefficient_16_1
compact_certificate_declaration theorem coefficient_16_2 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[2]?=some 0 := by
  change some (((((((d0_13_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_15_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_16_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_16_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_16_2 y z w b u))+(((d2_0_1 y z w b u)*(d3_16_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_15_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_15_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_15_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_14_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_14_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_14_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_13_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_13_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_13_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_12_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_12_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_12_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_11_2 y z w b u))+((d2_5_1 y z w b u)*(d3_11_1 y z w b u)))+((d2_6_0 y z w b u)*(d3_10_2 y z w b u)))))))))+((-1)*(d4_16_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_2,d0_14_2,d0_15_1,d0_15_2,d0_16_1,d0_16_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_2,d3_11_1,d3_11_2,d3_12_0,d3_12_1,d3_12_2,d3_13_0,d3_13_1,d3_13_2,d3_14_0,d3_14_1,d3_14_2,d3_15_0,d3_15_1,d3_15_2,d3_16_0,d3_16_1,d3_16_2,d4_16_2]
  ring
#print axioms coefficient_16_2

compact_certificate_declaration theorem coefficient_16_3 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[3]?=some 0 := by
  change some (((((((d0_13_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_15_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_16_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_16_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_16_2 y z w b u))+(((d2_0_2 y z w b u)*(d3_16_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_1_0 y z w b u)*(d3_15_3 y z w b u))+(((d2_1_1 y z w b u)*(d3_15_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_15_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_15_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_14_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_14_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_14_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_14_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_13_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_13_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_13_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_13_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_12_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_12_2 y z w b u))+((d2_4_2 y z w b u)*(d3_12_1 y z w b u))))+((((d2_5_0 y z w b u)*(d3_11_3 y z w b u))+((d2_5_1 y z w b u)*(d3_11_2 y z w b u)))+((d2_6_0 y z w b u)*(d3_10_3 y z w b u)))))))))+((-1)*(d4_16_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_3,d0_14_3,d0_15_2,d0_15_3,d0_16_2,d0_16_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_0_3,d2_1_0,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_3,d3_11_2,d3_11_3,d3_12_1,d3_12_2,d3_12_3,d3_13_0,d3_13_1,d3_13_2,d3_13_3,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_16_0,d3_16_1,d3_16_2,d4_16_3]
  ring
#print axioms coefficient_16_3
compact_certificate_declaration theorem coefficient_16_4 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[4]?=some 0 := by
  change some (((((((d0_13_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_15_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_16_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_16_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_16_2 y z w b u))+((d2_0_3 y z w b u)*(d3_16_1 y z w b u)))+((((d2_1_1 y z w b u)*(d3_15_3 y z w b u))+(((d2_1_2 y z w b u)*(d3_15_2 y z w b u))+((d2_1_3 y z w b u)*(d3_15_1 y z w b u))))+((((d2_2_0 y z w b u)*(d3_14_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_14_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_14_2 y z w b u))+((d2_2_3 y z w b u)*(d3_14_1 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_13_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_13_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_13_2 y z w b u))+((d2_3_3 y z w b u)*(d3_13_1 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_12_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_12_3 y z w b u))+((d2_4_2 y z w b u)*(d3_12_2 y z w b u))))+((((d2_5_0 y z w b u)*(d3_11_4 y z w b u))+((d2_5_1 y z w b u)*(d3_11_3 y z w b u)))+((d2_6_0 y z w b u)*(d3_10_4 y z w b u)))))))))+((-1)*(d4_16_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_4,d0_14_4,d0_15_3,d0_15_4,d0_16_3,d0_16_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_4,d3_11_3,d3_11_4,d3_12_2,d3_12_3,d3_12_4,d3_13_1,d3_13_2,d3_13_3,d3_13_4,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_1,d3_15_2,d3_15_3,d3_16_1,d3_16_2,d4_16_4]
  ring
#print axioms coefficient_16_4
compact_certificate_declaration theorem coefficient_16_5 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[5]?=some 0 := by
  change some (((((((d0_13_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_15_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_16_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_16_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_0_3 y z w b u)*(d3_16_2 y z w b u))+((((d2_1_2 y z w b u)*(d3_15_3 y z w b u))+((d2_1_3 y z w b u)*(d3_15_2 y z w b u)))+((((d2_2_1 y z w b u)*(d3_14_4 y z w b u))+(((d2_2_2 y z w b u)*(d3_14_3 y z w b u))+((d2_2_3 y z w b u)*(d3_14_2 y z w b u))))+((((d2_3_1 y z w b u)*(d3_13_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_13_3 y z w b u))+((d2_3_3 y z w b u)*(d3_13_2 y z w b u))))+((((d2_4_0 y z w b u)*(d3_12_5 y z w b u))+(((d2_4_1 y z w b u)*(d3_12_4 y z w b u))+((d2_4_2 y z w b u)*(d3_12_3 y z w b u))))+((((d2_5_0 y z w b u)*(d3_11_5 y z w b u))+((d2_5_1 y z w b u)*(d3_11_4 y z w b u)))+((d2_6_0 y z w b u)*(d3_10_5 y z w b u)))))))))+((-1)*(d4_16_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_5,d0_14_5,d0_15_4,d0_15_5,d0_16_4,d0_16_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_5,d3_11_4,d3_11_5,d3_12_3,d3_12_4,d3_12_5,d3_13_2,d3_13_3,d3_13_4,d3_14_2,d3_14_3,d3_14_4,d3_15_2,d3_15_3,d3_16_2,d4_16_5]
  ring
#print axioms coefficient_16_5

compact_certificate_declaration theorem coefficient_16_6 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[6]?=some 0 := by
  change some (((((((d0_13_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_15_6 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_16_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_16_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_1_3 y z w b u)*(d3_15_3 y z w b u))+((((d2_2_2 y z w b u)*(d3_14_4 y z w b u))+((d2_2_3 y z w b u)*(d3_14_3 y z w b u)))+((((d2_3_2 y z w b u)*(d3_13_4 y z w b u))+((d2_3_3 y z w b u)*(d3_13_3 y z w b u)))+((((d2_4_1 y z w b u)*(d3_12_5 y z w b u))+((d2_4_2 y z w b u)*(d3_12_4 y z w b u)))+((((d2_5_0 y z w b u)*(d3_11_6 y z w b u))+((d2_5_1 y z w b u)*(d3_11_5 y z w b u)))+((d2_6_0 y z w b u)*(d3_10_6 y z w b u))))))))+((-1)*(d4_16_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_6,d0_14_6,d0_15_5,d0_15_6,d0_16_5,d0_16_6,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_1_3,d2_2_2,d2_2_3,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_10_6,d3_11_5,d3_11_6,d3_12_4,d3_12_5,d3_13_3,d3_13_4,d3_14_3,d3_14_4,d3_15_3,d4_16_6]
  ring
#print axioms coefficient_16_6
compact_certificate_declaration theorem coefficient_16_7 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[7]?=some 0 := by
  change some (((((((d0_13_7 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_7 y z w b u)*(d1_2_0 y z w b u))+0)+(((d0_15_6 y z w b u)*(d1_1_1 y z w b u))+((d0_16_6 y z w b u)*(d1_0_1 y z w b u)))))+(((d2_2_3 y z w b u)*(d3_14_4 y z w b u))+(((d2_3_3 y z w b u)*(d3_13_4 y z w b u))+(((d2_4_2 y z w b u)*(d3_12_5 y z w b u))+((d2_5_1 y z w b u)*(d3_11_6 y z w b u))))))+((-1)*(d4_16_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_7,d0_14_7,d0_15_6,d0_16_6,d1_0_1,d1_1_1,d1_2_0,d1_3_0,d2_2_3,d2_3_3,d2_4_2,d2_5_1,d3_11_6,d3_12_5,d3_13_4,d3_14_4,d4_16_7]
  ring
#print axioms coefficient_16_7

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_17 (y z w b u : ℂ) : (innerCertificate17 y z w b u).length=8 := by
  norm_num [innerCertificate17,add,multiply,scale,inner0_14,inner0_15,inner0_16,inner0_17,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner4_17]
compact_certificate_declaration theorem inner_eval_17 (y z w a b u : ℂ) :
    evaluate a (innerCertificate17 y z w b u)=(((((c0_14 y z w a b u)*(c1_3 y z w a b u))+(((c0_15 y z w a b u)*(c1_2 y z w a b u))+(((c0_16 y z w a b u)*(c1_1 y z w a b u))+(((c0_17 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_17 y z w a b u))+(((c2_1 y z w a b u)*(c3_16 y z w a b u))+(((c2_2 y z w a b u)*(c3_15 y z w a b u))+(((c2_3 y z w a b u)*(c3_14 y z w a b u))+(((c2_4 y z w a b u)*(c3_13 y z w a b u))+(((c2_5 y z w a b u)*(c3_12 y z w a b u))+((c2_6 y z w a b u)*(c3_11 y z w a b u)))))))))+((-1)*(c4_17 y z w a b u))) := by
  simp only [innerCertificate17,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_14,c0_15,c0_16,c0_17,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c4_17]
#print axioms inner_eval_17

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_17_0 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[0]?=some 0 := by
  change some (((((((d0_14_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_17_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_0_0 y z w b u)*(d3_17_0 y z w b u))+0)+((((d2_1_0 y z w b u)*(d3_16_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_15_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_14_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_13_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_12_0 y z w b u))+0)+(((d2_6_0 y z w b u)*(d3_11_0 y z w b u))+0))))))))+(((-1)*(d4_17_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_0,d0_15_0,d0_16_0,d0_17_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_0_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d3_11_0,d3_12_0,d3_13_0,d3_14_0,d3_15_0,d3_16_0,d3_17_0,d4_17_0]
  ring
#print axioms coefficient_17_0
compact_certificate_declaration theorem coefficient_17_1 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[1]?=some 0 := by
  change some (((((((d0_14_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_16_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_17_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_17_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_0 y z w b u)*(d3_17_1 y z w b u))+(((d2_0_1 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_16_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_16_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_15_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_15_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_14_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_14_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_13_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_13_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_12_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_12_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_11_1 y z w b u)))))))))+((-1)*(d4_17_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_1,d0_15_1,d0_16_0,d0_16_1,d0_17_0,d0_17_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_0,d2_0_1,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d3_11_1,d3_12_0,d3_12_1,d3_13_0,d3_13_1,d3_14_0,d3_14_1,d3_15_0,d3_15_1,d3_16_0,d3_16_1,d3_17_0,d3_17_1,d4_17_1]
  ring
#print axioms coefficient_17_1
compact_certificate_declaration theorem coefficient_17_2 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[2]?=some 0 := by
  change some (((((((d0_14_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_16_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_17_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_17_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_1 y z w b u)*(d3_17_1 y z w b u))+(((d2_0_2 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_1_0 y z w b u)*(d3_16_2 y z w b u))+(((d2_1_1 y z w b u)*(d3_16_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_15_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_15_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_15_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_14_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_14_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_14_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_13_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_13_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_13_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_12_2 y z w b u))+((d2_5_1 y z w b u)*(d3_12_1 y z w b u)))+((d2_6_0 y z w b u)*(d3_11_2 y z w b u)))))))))+((-1)*(d4_17_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_2,d0_15_2,d0_16_1,d0_16_2,d0_17_1,d0_17_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_1,d2_0_2,d2_1_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_11_2,d3_12_1,d3_12_2,d3_13_0,d3_13_1,d3_13_2,d3_14_0,d3_14_1,d3_14_2,d3_15_0,d3_15_1,d3_15_2,d3_16_0,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d4_17_2]
  ring
#print axioms coefficient_17_2

compact_certificate_declaration theorem coefficient_17_3 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[3]?=some 0 := by
  change some (((((((d0_14_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_16_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_17_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_17_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_0_2 y z w b u)*(d3_17_1 y z w b u))+(((d2_0_3 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_1_1 y z w b u)*(d3_16_2 y z w b u))+(((d2_1_2 y z w b u)*(d3_16_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_15_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_15_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_15_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_15_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_14_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_14_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_14_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_14_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_13_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_13_2 y z w b u))+((d2_4_2 y z w b u)*(d3_13_1 y z w b u))))+((((d2_5_0 y z w b u)*(d3_12_3 y z w b u))+((d2_5_1 y z w b u)*(d3_12_2 y z w b u)))+((d2_6_0 y z w b u)*(d3_11_3 y z w b u)))))))))+((-1)*(d4_17_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_3,d0_15_3,d0_16_2,d0_16_3,d0_17_2,d0_17_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_2,d2_0_3,d2_1_1,d2_1_2,d2_1_3,d2_2_0,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_11_3,d3_12_2,d3_12_3,d3_13_1,d3_13_2,d3_13_3,d3_14_0,d3_14_1,d3_14_2,d3_14_3,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_16_0,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d4_17_3]
  ring
#print axioms coefficient_17_3
compact_certificate_declaration theorem coefficient_17_4 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[4]?=some 0 := by
  change some (((((((d0_14_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_16_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_17_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_17_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_0_3 y z w b u)*(d3_17_1 y z w b u))+((((d2_1_2 y z w b u)*(d3_16_2 y z w b u))+((d2_1_3 y z w b u)*(d3_16_1 y z w b u)))+((((d2_2_1 y z w b u)*(d3_15_3 y z w b u))+(((d2_2_2 y z w b u)*(d3_15_2 y z w b u))+((d2_2_3 y z w b u)*(d3_15_1 y z w b u))))+((((d2_3_0 y z w b u)*(d3_14_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_14_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_14_2 y z w b u))+((d2_3_3 y z w b u)*(d3_14_1 y z w b u)))))+((((d2_4_0 y z w b u)*(d3_13_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_13_3 y z w b u))+((d2_4_2 y z w b u)*(d3_13_2 y z w b u))))+((((d2_5_0 y z w b u)*(d3_12_4 y z w b u))+((d2_5_1 y z w b u)*(d3_12_3 y z w b u)))+((d2_6_0 y z w b u)*(d3_11_4 y z w b u)))))))))+((-1)*(d4_17_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_4,d0_15_4,d0_16_3,d0_16_4,d0_17_3,d0_17_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_0_3,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_11_4,d3_12_3,d3_12_4,d3_13_2,d3_13_3,d3_13_4,d3_14_1,d3_14_2,d3_14_3,d3_14_4,d3_15_1,d3_15_2,d3_15_3,d3_16_1,d3_16_2,d3_17_1,d4_17_4]
  ring
#print axioms coefficient_17_4
compact_certificate_declaration theorem coefficient_17_5 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[5]?=some 0 := by
  change some (((((((d0_14_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_16_5 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_17_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_17_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_1_3 y z w b u)*(d3_16_2 y z w b u))+((((d2_2_2 y z w b u)*(d3_15_3 y z w b u))+((d2_2_3 y z w b u)*(d3_15_2 y z w b u)))+((((d2_3_1 y z w b u)*(d3_14_4 y z w b u))+(((d2_3_2 y z w b u)*(d3_14_3 y z w b u))+((d2_3_3 y z w b u)*(d3_14_2 y z w b u))))+((((d2_4_1 y z w b u)*(d3_13_4 y z w b u))+((d2_4_2 y z w b u)*(d3_13_3 y z w b u)))+((((d2_5_0 y z w b u)*(d3_12_5 y z w b u))+((d2_5_1 y z w b u)*(d3_12_4 y z w b u)))+((d2_6_0 y z w b u)*(d3_11_5 y z w b u))))))))+((-1)*(d4_17_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_5,d0_15_5,d0_16_4,d0_16_5,d0_17_4,d0_17_5,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_1_3,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_11_5,d3_12_4,d3_12_5,d3_13_3,d3_13_4,d3_14_2,d3_14_3,d3_14_4,d3_15_2,d3_15_3,d3_16_2,d4_17_5]
  ring
#print axioms coefficient_17_5

compact_certificate_declaration theorem coefficient_17_6 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[6]?=some 0 := by
  change some (((((((d0_14_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_6 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_16_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_16_6 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_17_5 y z w b u)*(d1_0_1 y z w b u)))))+(((d2_2_3 y z w b u)*(d3_15_3 y z w b u))+((((d2_3_2 y z w b u)*(d3_14_4 y z w b u))+((d2_3_3 y z w b u)*(d3_14_3 y z w b u)))+(((d2_4_2 y z w b u)*(d3_13_4 y z w b u))+(((d2_5_1 y z w b u)*(d3_12_5 y z w b u))+((d2_6_0 y z w b u)*(d3_11_6 y z w b u)))))))+((-1)*(d4_17_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_6,d0_15_6,d0_16_5,d0_16_6,d0_17_5,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_2_3,d2_3_2,d2_3_3,d2_4_2,d2_5_1,d2_6_0,d3_11_6,d3_12_5,d3_13_4,d3_14_3,d3_14_4,d3_15_3,d4_17_6]
  ring
#print axioms coefficient_17_6
compact_certificate_declaration theorem coefficient_17_7 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[7]?=some 0 := by
  change some ((((((d0_14_7 y z w b u)*(d1_3_0 y z w b u))+0)+((d0_16_6 y z w b u)*(d1_1_1 y z w b u)))+((d2_3_3 y z w b u)*(d3_14_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_7,d0_16_6,d1_1_1,d1_3_0,d2_3_3,d3_14_4]
  ring
#print axioms coefficient_17_7

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_18 (y z w b u : ℂ) : (innerCertificate18 y z w b u).length=7 := by
  norm_num [innerCertificate18,add,multiply,scale,inner0_15,inner0_16,inner0_17,inner0_18,inner1_0,inner1_1,inner1_2,inner1_3,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner4_18]
compact_certificate_declaration theorem inner_eval_18 (y z w a b u : ℂ) :
    evaluate a (innerCertificate18 y z w b u)=(((((c0_15 y z w a b u)*(c1_3 y z w a b u))+(((c0_16 y z w a b u)*(c1_2 y z w a b u))+(((c0_17 y z w a b u)*(c1_1 y z w a b u))+(((c0_18 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_1 y z w a b u)*(c3_17 y z w a b u))+(((c2_2 y z w a b u)*(c3_16 y z w a b u))+(((c2_3 y z w a b u)*(c3_15 y z w a b u))+(((c2_4 y z w a b u)*(c3_14 y z w a b u))+(((c2_5 y z w a b u)*(c3_13 y z w a b u))+((c2_6 y z w a b u)*(c3_12 y z w a b u))))))))+((-1)*(c4_18 y z w a b u))) := by
  simp only [innerCertificate18,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_15,c0_16,c0_17,c0_18,c1_0,c1_1,c1_2,c1_3,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c4_18]
#print axioms inner_eval_18

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_18_0 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[0]?=some 0 := by
  change some (((((((d0_15_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_17_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_18_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_1_0 y z w b u)*(d3_17_0 y z w b u))+0)+((((d2_2_0 y z w b u)*(d3_16_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_15_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_14_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_13_0 y z w b u))+0)+(((d2_6_0 y z w b u)*(d3_12_0 y z w b u))+0)))))))+(((-1)*(d4_18_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_0,d0_16_0,d0_17_0,d0_18_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d3_12_0,d3_13_0,d3_14_0,d3_15_0,d3_16_0,d3_17_0,d4_18_0]
  ring
#print axioms coefficient_18_0
compact_certificate_declaration theorem coefficient_18_1 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[1]?=some 0 := by
  change some (((((((d0_15_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_17_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_17_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_18_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_18_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_1_0 y z w b u)*(d3_17_1 y z w b u))+(((d2_1_1 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_16_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_16_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_15_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_15_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_14_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_14_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_13_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_13_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_12_1 y z w b u))))))))+((-1)*(d4_18_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_1,d0_16_1,d0_17_0,d0_17_1,d0_18_0,d0_18_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_1_0,d2_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d3_12_1,d3_13_0,d3_13_1,d3_14_0,d3_14_1,d3_15_0,d3_15_1,d3_16_0,d3_16_1,d3_17_0,d3_17_1,d4_18_1]
  ring
#print axioms coefficient_18_1
compact_certificate_declaration theorem coefficient_18_2 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[2]?=some 0 := by
  change some (((((((d0_15_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_17_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_17_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_18_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_18_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_1_1 y z w b u)*(d3_17_1 y z w b u))+(((d2_1_2 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_16_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_16_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_15_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_15_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_15_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_14_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_14_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_14_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_13_2 y z w b u))+((d2_5_1 y z w b u)*(d3_13_1 y z w b u)))+((d2_6_0 y z w b u)*(d3_12_2 y z w b u))))))))+((-1)*(d4_18_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_2,d0_16_2,d0_17_1,d0_17_2,d0_18_1,d0_18_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_1_1,d2_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_12_2,d3_13_1,d3_13_2,d3_14_0,d3_14_1,d3_14_2,d3_15_0,d3_15_1,d3_15_2,d3_16_0,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d4_18_2]
  ring
#print axioms coefficient_18_2

compact_certificate_declaration theorem coefficient_18_3 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[3]?=some 0 := by
  change some (((((((d0_15_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_17_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_17_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_18_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_18_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_1_2 y z w b u)*(d3_17_1 y z w b u))+(((d2_1_3 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_2_1 y z w b u)*(d3_16_2 y z w b u))+(((d2_2_2 y z w b u)*(d3_16_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_15_3 y z w b u))+(((d2_3_1 y z w b u)*(d3_15_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_15_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_15_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_14_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_14_2 y z w b u))+((d2_4_2 y z w b u)*(d3_14_1 y z w b u))))+((((d2_5_0 y z w b u)*(d3_13_3 y z w b u))+((d2_5_1 y z w b u)*(d3_13_2 y z w b u)))+((d2_6_0 y z w b u)*(d3_12_3 y z w b u))))))))+((-1)*(d4_18_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_3,d0_16_3,d0_17_2,d0_17_3,d0_18_2,d0_18_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_1_2,d2_1_3,d2_2_1,d2_2_2,d2_2_3,d2_3_0,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_12_3,d3_13_2,d3_13_3,d3_14_1,d3_14_2,d3_14_3,d3_15_0,d3_15_1,d3_15_2,d3_15_3,d3_16_0,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d4_18_3]
  ring
#print axioms coefficient_18_3
compact_certificate_declaration theorem coefficient_18_4 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[4]?=some 0 := by
  change some (((((((d0_15_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_17_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_17_4 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_18_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_18_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+(((d2_1_3 y z w b u)*(d3_17_1 y z w b u))+((((d2_2_2 y z w b u)*(d3_16_2 y z w b u))+((d2_2_3 y z w b u)*(d3_16_1 y z w b u)))+((((d2_3_1 y z w b u)*(d3_15_3 y z w b u))+(((d2_3_2 y z w b u)*(d3_15_2 y z w b u))+((d2_3_3 y z w b u)*(d3_15_1 y z w b u))))+((((d2_4_0 y z w b u)*(d3_14_4 y z w b u))+(((d2_4_1 y z w b u)*(d3_14_3 y z w b u))+((d2_4_2 y z w b u)*(d3_14_2 y z w b u))))+((((d2_5_0 y z w b u)*(d3_13_4 y z w b u))+((d2_5_1 y z w b u)*(d3_13_3 y z w b u)))+((d2_6_0 y z w b u)*(d3_12_4 y z w b u))))))))+((-1)*(d4_18_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_4,d0_16_4,d0_17_3,d0_17_4,d0_18_3,d0_18_4,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_1_3,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_12_4,d3_13_3,d3_13_4,d3_14_2,d3_14_3,d3_14_4,d3_15_1,d3_15_2,d3_15_3,d3_16_1,d3_16_2,d3_17_1,d4_18_4]
  ring
#print axioms coefficient_18_4
compact_certificate_declaration theorem coefficient_18_5 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[5]?=some 0 := by
  change some (((((((d0_15_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_5 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_17_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_17_5 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_18_4 y z w b u)*(d1_0_1 y z w b u)))))+(((d2_2_3 y z w b u)*(d3_16_2 y z w b u))+((((d2_3_2 y z w b u)*(d3_15_3 y z w b u))+((d2_3_3 y z w b u)*(d3_15_2 y z w b u)))+((((d2_4_1 y z w b u)*(d3_14_4 y z w b u))+((d2_4_2 y z w b u)*(d3_14_3 y z w b u)))+(((d2_5_1 y z w b u)*(d3_13_4 y z w b u))+((d2_6_0 y z w b u)*(d3_12_5 y z w b u)))))))+((-1)*(d4_18_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_5,d0_16_5,d0_17_4,d0_17_5,d0_18_4,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_2_3,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d2_5_1,d2_6_0,d3_12_5,d3_13_4,d3_14_3,d3_14_4,d3_15_2,d3_15_3,d3_16_2,d4_18_5]
  ring
#print axioms coefficient_18_5

compact_certificate_declaration theorem coefficient_18_6 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[6]?=some 0 := by
  change some (((((((d0_15_6 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_16_6 y z w b u)*(d1_2_0 y z w b u))+0)+((d0_17_5 y z w b u)*(d1_1_1 y z w b u))))+(((d2_3_3 y z w b u)*(d3_15_3 y z w b u))+((d2_4_2 y z w b u)*(d3_14_4 y z w b u))))+((-1)*(d4_18_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_6,d0_16_6,d0_17_5,d1_1_1,d1_2_0,d1_3_0,d2_3_3,d2_4_2,d3_14_4,d3_15_3,d4_18_6]
  ring
#print axioms coefficient_18_6

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_19 (y z w b u : ℂ) : (innerCertificate19 y z w b u).length=7 := by
  norm_num [innerCertificate19,add,multiply,scale,inner0_16,inner0_17,inner0_18,inner0_19,inner1_0,inner1_1,inner1_2,inner1_3,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner4_19]
compact_certificate_declaration theorem inner_eval_19 (y z w a b u : ℂ) :
    evaluate a (innerCertificate19 y z w b u)=(((((c0_16 y z w a b u)*(c1_3 y z w a b u))+(((c0_17 y z w a b u)*(c1_2 y z w a b u))+(((c0_18 y z w a b u)*(c1_1 y z w a b u))+(((c0_19 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_2 y z w a b u)*(c3_17 y z w a b u))+(((c2_3 y z w a b u)*(c3_16 y z w a b u))+(((c2_4 y z w a b u)*(c3_15 y z w a b u))+(((c2_5 y z w a b u)*(c3_14 y z w a b u))+((c2_6 y z w a b u)*(c3_13 y z w a b u)))))))+((-1)*(c4_19 y z w a b u))) := by
  simp only [innerCertificate19,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_16,c0_17,c0_18,c0_19,c1_0,c1_1,c1_2,c1_3,c2_2,c2_3,c2_4,c2_5,c2_6,c3_13,c3_14,c3_15,c3_16,c3_17,c4_19]
#print axioms inner_eval_19

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_19_0 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[0]?=some 0 := by
  change some (((((((d0_16_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_17_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_18_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_19_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_17_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_16_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_15_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_14_0 y z w b u))+0)+(((d2_6_0 y z w b u)*(d3_13_0 y z w b u))+0))))))+(((-1)*(d4_19_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_0,d0_17_0,d0_18_0,d0_19_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d3_13_0,d3_14_0,d3_15_0,d3_16_0,d3_17_0,d4_19_0]
  ring
#print axioms coefficient_19_0
compact_certificate_declaration theorem coefficient_19_1 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[1]?=some 0 := by
  change some (((((((d0_16_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_17_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_18_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_18_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_19_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_19_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_2_0 y z w b u)*(d3_17_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_16_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_16_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_15_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_15_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_14_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_14_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_13_1 y z w b u)))))))+((-1)*(d4_19_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_1,d0_17_1,d0_18_0,d0_18_1,d0_19_0,d0_19_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d3_13_1,d3_14_0,d3_14_1,d3_15_0,d3_15_1,d3_16_0,d3_16_1,d3_17_0,d3_17_1,d4_19_1]
  ring
#print axioms coefficient_19_1
compact_certificate_declaration theorem coefficient_19_2 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[2]?=some 0 := by
  change some (((((((d0_16_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_17_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_18_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_18_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_19_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_19_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_2_1 y z w b u)*(d3_17_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_16_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_16_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_15_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_15_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_15_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_14_2 y z w b u))+((d2_5_1 y z w b u)*(d3_14_1 y z w b u)))+((d2_6_0 y z w b u)*(d3_13_2 y z w b u)))))))+((-1)*(d4_19_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_2,d0_17_2,d0_18_1,d0_18_2,d0_19_1,d0_19_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_13_2,d3_14_1,d3_14_2,d3_15_0,d3_15_1,d3_15_2,d3_16_0,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d4_19_2]
  ring
#print axioms coefficient_19_2

compact_certificate_declaration theorem coefficient_19_3 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[3]?=some 0 := by
  change some (((((((d0_16_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_17_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_18_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_18_3 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_19_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_19_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_2_2 y z w b u)*(d3_17_1 y z w b u))+(((d2_2_3 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_3_1 y z w b u)*(d3_16_2 y z w b u))+(((d2_3_2 y z w b u)*(d3_16_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_4_0 y z w b u)*(d3_15_3 y z w b u))+(((d2_4_1 y z w b u)*(d3_15_2 y z w b u))+((d2_4_2 y z w b u)*(d3_15_1 y z w b u))))+((((d2_5_0 y z w b u)*(d3_14_3 y z w b u))+((d2_5_1 y z w b u)*(d3_14_2 y z w b u)))+((d2_6_0 y z w b u)*(d3_13_3 y z w b u)))))))+((-1)*(d4_19_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_3,d0_17_3,d0_18_2,d0_18_3,d0_19_2,d0_19_3,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_2_2,d2_2_3,d2_3_1,d2_3_2,d2_3_3,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_13_3,d3_14_2,d3_14_3,d3_15_1,d3_15_2,d3_15_3,d3_16_0,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d4_19_3]
  ring
#print axioms coefficient_19_3
compact_certificate_declaration theorem coefficient_19_4 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[4]?=some 0 := by
  change some (((((((d0_16_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_17_4 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_18_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_18_4 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_19_3 y z w b u)*(d1_0_1 y z w b u)))))+(((d2_2_3 y z w b u)*(d3_17_1 y z w b u))+((((d2_3_2 y z w b u)*(d3_16_2 y z w b u))+((d2_3_3 y z w b u)*(d3_16_1 y z w b u)))+((((d2_4_1 y z w b u)*(d3_15_3 y z w b u))+((d2_4_2 y z w b u)*(d3_15_2 y z w b u)))+((((d2_5_0 y z w b u)*(d3_14_4 y z w b u))+((d2_5_1 y z w b u)*(d3_14_3 y z w b u)))+((d2_6_0 y z w b u)*(d3_13_4 y z w b u)))))))+((-1)*(d4_19_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_4,d0_17_4,d0_18_3,d0_18_4,d0_19_3,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_2_3,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_13_4,d3_14_3,d3_14_4,d3_15_2,d3_15_3,d3_16_1,d3_16_2,d3_17_1,d4_19_4]
  ring
#print axioms coefficient_19_4
compact_certificate_declaration theorem coefficient_19_5 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[5]?=some 0 := by
  change some (((((((d0_16_5 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_17_5 y z w b u)*(d1_2_0 y z w b u))+0)+((d0_18_4 y z w b u)*(d1_1_1 y z w b u))))+(((d2_3_3 y z w b u)*(d3_16_2 y z w b u))+(((d2_4_2 y z w b u)*(d3_15_3 y z w b u))+((d2_5_1 y z w b u)*(d3_14_4 y z w b u)))))+((-1)*(d4_19_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_5,d0_17_5,d0_18_4,d1_1_1,d1_2_0,d1_3_0,d2_3_3,d2_4_2,d2_5_1,d3_14_4,d3_15_3,d3_16_2,d4_19_5]
  ring
#print axioms coefficient_19_5

compact_certificate_declaration theorem coefficient_19_6 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[6]?=some 0 := by
  change some (((((d0_16_6 y z w b u)*(d1_3_0 y z w b u))+0)+((-1)*(d4_19_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_6,d1_3_0,d4_19_6]
  ring
#print axioms coefficient_19_6

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_20 (y z w b u : ℂ) : (innerCertificate20 y z w b u).length=6 := by
  norm_num [innerCertificate20,add,multiply,scale,inner0_17,inner0_18,inner0_19,inner0_20,inner1_0,inner1_1,inner1_2,inner1_3,inner2_3,inner2_4,inner2_5,inner2_6,inner3_14,inner3_15,inner3_16,inner3_17,inner4_20]
compact_certificate_declaration theorem inner_eval_20 (y z w a b u : ℂ) :
    evaluate a (innerCertificate20 y z w b u)=(((((c0_17 y z w a b u)*(c1_3 y z w a b u))+(((c0_18 y z w a b u)*(c1_2 y z w a b u))+(((c0_19 y z w a b u)*(c1_1 y z w a b u))+(((c0_20 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_3 y z w a b u)*(c3_17 y z w a b u))+(((c2_4 y z w a b u)*(c3_16 y z w a b u))+(((c2_5 y z w a b u)*(c3_15 y z w a b u))+((c2_6 y z w a b u)*(c3_14 y z w a b u))))))+((-1)*(c4_20 y z w a b u))) := by
  simp only [innerCertificate20,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_17,c0_18,c0_19,c0_20,c1_0,c1_1,c1_2,c1_3,c2_3,c2_4,c2_5,c2_6,c3_14,c3_15,c3_16,c3_17,c4_20]
#print axioms inner_eval_20

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_20_0 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[0]?=some 0 := by
  change some (((((((d0_17_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_18_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_19_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_20_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_17_0 y z w b u))+0)+((((d2_4_0 y z w b u)*(d3_16_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_15_0 y z w b u))+0)+(((d2_6_0 y z w b u)*(d3_14_0 y z w b u))+0)))))+(((-1)*(d4_20_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_17_0,d0_18_0,d0_19_0,d0_20_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d3_14_0,d3_15_0,d3_16_0,d3_17_0,d4_20_0]
  ring
#print axioms coefficient_20_0
compact_certificate_declaration theorem coefficient_20_1 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[1]?=some 0 := by
  change some (((((((d0_17_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_18_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_19_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_19_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_20_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_20_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_3_0 y z w b u)*(d3_17_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_16_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_16_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_15_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_15_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_14_1 y z w b u))))))+((-1)*(d4_20_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_17_1,d0_18_1,d0_19_0,d0_19_1,d0_20_0,d0_20_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_3_0,d2_3_1,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d3_14_1,d3_15_0,d3_15_1,d3_16_0,d3_16_1,d3_17_0,d3_17_1,d4_20_1]
  ring
#print axioms coefficient_20_1
compact_certificate_declaration theorem coefficient_20_2 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[2]?=some 0 := by
  change some (((((((d0_17_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_18_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_19_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_19_2 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_20_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_20_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_3_1 y z w b u)*(d3_17_1 y z w b u))+(((d2_3_2 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_4_0 y z w b u)*(d3_16_2 y z w b u))+(((d2_4_1 y z w b u)*(d3_16_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_16_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_15_2 y z w b u))+((d2_5_1 y z w b u)*(d3_15_1 y z w b u)))+((d2_6_0 y z w b u)*(d3_14_2 y z w b u))))))+((-1)*(d4_20_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_17_2,d0_18_2,d0_19_1,d0_19_2,d0_20_1,d0_20_2,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_3_1,d2_3_2,d2_4_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_14_2,d3_15_1,d3_15_2,d3_16_0,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d4_20_2]
  ring
#print axioms coefficient_20_2

compact_certificate_declaration theorem coefficient_20_3 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[3]?=some 0 := by
  change some (((((((d0_17_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_18_3 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_19_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_19_3 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_20_2 y z w b u)*(d1_0_1 y z w b u)))))+((((d2_3_2 y z w b u)*(d3_17_1 y z w b u))+(((d2_3_3 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_4_1 y z w b u)*(d3_16_2 y z w b u))+((d2_4_2 y z w b u)*(d3_16_1 y z w b u)))+((((d2_5_0 y z w b u)*(d3_15_3 y z w b u))+((d2_5_1 y z w b u)*(d3_15_2 y z w b u)))+((d2_6_0 y z w b u)*(d3_14_3 y z w b u))))))+((-1)*(d4_20_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_17_3,d0_18_3,d0_19_2,d0_19_3,d0_20_2,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_3_2,d2_3_3,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_14_3,d3_15_2,d3_15_3,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d4_20_3]
  ring
#print axioms coefficient_20_3
compact_certificate_declaration theorem coefficient_20_4 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[4]?=some 0 := by
  change some (((((((d0_17_4 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_18_4 y z w b u)*(d1_2_0 y z w b u))+0)+((d0_19_3 y z w b u)*(d1_1_1 y z w b u))))+(((d2_3_3 y z w b u)*(d3_17_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_16_2 y z w b u))+(((d2_5_1 y z w b u)*(d3_15_3 y z w b u))+((d2_6_0 y z w b u)*(d3_14_4 y z w b u))))))+((-1)*(d4_20_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_17_4,d0_18_4,d0_19_3,d1_1_1,d1_2_0,d1_3_0,d2_3_3,d2_4_2,d2_5_1,d2_6_0,d3_14_4,d3_15_3,d3_16_2,d3_17_1,d4_20_4]
  ring
#print axioms coefficient_20_4
compact_certificate_declaration theorem coefficient_20_5 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[5]?=some 0 := by
  change some (((((d0_17_5 y z w b u)*(d1_3_0 y z w b u))+0)+((-1)*(d4_20_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_17_5,d1_3_0,d4_20_5]
  ring
#print axioms coefficient_20_5

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_21 (y z w b u : ℂ) : (innerCertificate21 y z w b u).length=5 := by
  norm_num [innerCertificate21,add,multiply,scale,inner0_18,inner0_19,inner0_20,inner0_21,inner1_0,inner1_1,inner1_2,inner1_3,inner2_4,inner2_5,inner2_6,inner3_15,inner3_16,inner3_17,inner4_21]
compact_certificate_declaration theorem inner_eval_21 (y z w a b u : ℂ) :
    evaluate a (innerCertificate21 y z w b u)=(((((c0_18 y z w a b u)*(c1_3 y z w a b u))+(((c0_19 y z w a b u)*(c1_2 y z w a b u))+(((c0_20 y z w a b u)*(c1_1 y z w a b u))+(((c0_21 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_4 y z w a b u)*(c3_17 y z w a b u))+(((c2_5 y z w a b u)*(c3_16 y z w a b u))+((c2_6 y z w a b u)*(c3_15 y z w a b u)))))+((-1)*(c4_21 y z w a b u))) := by
  simp only [innerCertificate21,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_18,c0_19,c0_20,c0_21,c1_0,c1_1,c1_2,c1_3,c2_4,c2_5,c2_6,c3_15,c3_16,c3_17,c4_21]
#print axioms inner_eval_21

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_21_0 (y z w b u : ℂ) :
    (innerCertificate21 y z w b u)[0]?=some 0 := by
  change some (((((((d0_18_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_19_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_20_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_21_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_4_0 y z w b u)*(d3_17_0 y z w b u))+0)+((((d2_5_0 y z w b u)*(d3_16_0 y z w b u))+0)+(((d2_6_0 y z w b u)*(d3_15_0 y z w b u))+0))))+(((-1)*(d4_21_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_18_0,d0_19_0,d0_20_0,d0_21_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_4_0,d2_5_0,d2_6_0,d3_15_0,d3_16_0,d3_17_0,d4_21_0]
  ring
#print axioms coefficient_21_0
compact_certificate_declaration theorem coefficient_21_1 (y z w b u : ℂ) :
    (innerCertificate21 y z w b u)[1]?=some 0 := by
  change some (((((((d0_18_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_19_1 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_20_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_20_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_21_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_21_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_4_0 y z w b u)*(d3_17_1 y z w b u))+(((d2_4_1 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_16_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_16_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_15_1 y z w b u)))))+((-1)*(d4_21_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_18_1,d0_19_1,d0_20_0,d0_20_1,d0_21_0,d0_21_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_4_0,d2_4_1,d2_5_0,d2_5_1,d2_6_0,d3_15_1,d3_16_0,d3_16_1,d3_17_0,d3_17_1,d4_21_1]
  ring
#print axioms coefficient_21_1
compact_certificate_declaration theorem coefficient_21_2 (y z w b u : ℂ) :
    (innerCertificate21 y z w b u)[2]?=some 0 := by
  change some (((((((d0_18_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_19_2 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_20_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_20_2 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_21_1 y z w b u)*(d1_0_1 y z w b u)))))+((((d2_4_1 y z w b u)*(d3_17_1 y z w b u))+(((d2_4_2 y z w b u)*(d3_17_0 y z w b u))+0))+((((d2_5_0 y z w b u)*(d3_16_2 y z w b u))+((d2_5_1 y z w b u)*(d3_16_1 y z w b u)))+((d2_6_0 y z w b u)*(d3_15_2 y z w b u)))))+((-1)*(d4_21_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_18_2,d0_19_2,d0_20_1,d0_20_2,d0_21_1,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_4_1,d2_4_2,d2_5_0,d2_5_1,d2_6_0,d3_15_2,d3_16_1,d3_16_2,d3_17_0,d3_17_1,d4_21_2]
  ring
#print axioms coefficient_21_2

compact_certificate_declaration theorem coefficient_21_3 (y z w b u : ℂ) :
    (innerCertificate21 y z w b u)[3]?=some 0 := by
  change some (((((((d0_18_3 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_19_3 y z w b u)*(d1_2_0 y z w b u))+0)+((d0_20_2 y z w b u)*(d1_1_1 y z w b u))))+(((d2_4_2 y z w b u)*(d3_17_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_16_2 y z w b u))+((d2_6_0 y z w b u)*(d3_15_3 y z w b u)))))+((-1)*(d4_21_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_18_3,d0_19_3,d0_20_2,d1_1_1,d1_2_0,d1_3_0,d2_4_2,d2_5_1,d2_6_0,d3_15_3,d3_16_2,d3_17_1,d4_21_3]
  ring
#print axioms coefficient_21_3
compact_certificate_declaration theorem coefficient_21_4 (y z w b u : ℂ) :
    (innerCertificate21 y z w b u)[4]?=some 0 := by
  change some (((((d0_18_4 y z w b u)*(d1_3_0 y z w b u))+0)+((-1)*(d4_21_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_18_4,d1_3_0,d4_21_4]
  ring
#print axioms coefficient_21_4

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_22 (y z w b u : ℂ) : (innerCertificate22 y z w b u).length=4 := by
  norm_num [innerCertificate22,add,multiply,scale,inner0_19,inner0_20,inner0_21,inner1_1,inner1_2,inner1_3,inner2_5,inner2_6,inner3_16,inner3_17,inner4_22]
compact_certificate_declaration theorem inner_eval_22 (y z w a b u : ℂ) :
    evaluate a (innerCertificate22 y z w b u)=(((((c0_19 y z w a b u)*(c1_3 y z w a b u))+(((c0_20 y z w a b u)*(c1_2 y z w a b u))+((c0_21 y z w a b u)*(c1_1 y z w a b u))))+(((c2_5 y z w a b u)*(c3_17 y z w a b u))+((c2_6 y z w a b u)*(c3_16 y z w a b u))))+((-1)*(c4_22 y z w a b u))) := by
  simp only [innerCertificate22,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_19,c0_20,c0_21,c1_1,c1_2,c1_3,c2_5,c2_6,c3_16,c3_17,c4_22]
#print axioms inner_eval_22

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_22_0 (y z w b u : ℂ) :
    (innerCertificate22 y z w b u)[0]?=some 0 := by
  change some (((((((d0_19_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_20_0 y z w b u)*(d1_2_0 y z w b u))+0)+(((d0_21_0 y z w b u)*(d1_1_0 y z w b u))+0)))+((((d2_5_0 y z w b u)*(d3_17_0 y z w b u))+0)+(((d2_6_0 y z w b u)*(d3_16_0 y z w b u))+0)))+(((-1)*(d4_22_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_19_0,d0_20_0,d0_21_0,d1_1_0,d1_2_0,d1_3_0,d2_5_0,d2_6_0,d3_16_0,d3_17_0,d4_22_0]
  ring
#print axioms coefficient_22_0
compact_certificate_declaration theorem coefficient_22_1 (y z w b u : ℂ) :
    (innerCertificate22 y z w b u)[1]?=some 0 := by
  change some (((((((d0_19_1 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_20_1 y z w b u)*(d1_2_0 y z w b u))+0)+(((d0_21_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_21_1 y z w b u)*(d1_1_0 y z w b u))+0))))+((((d2_5_0 y z w b u)*(d3_17_1 y z w b u))+(((d2_5_1 y z w b u)*(d3_17_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_16_1 y z w b u))))+((-1)*(d4_22_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_19_1,d0_20_1,d0_21_0,d0_21_1,d1_1_0,d1_1_1,d1_2_0,d1_3_0,d2_5_0,d2_5_1,d2_6_0,d3_16_1,d3_17_0,d3_17_1,d4_22_1]
  ring
#print axioms coefficient_22_1
compact_certificate_declaration theorem coefficient_22_2 (y z w b u : ℂ) :
    (innerCertificate22 y z w b u)[2]?=some 0 := by
  change some (((((((d0_19_2 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_20_2 y z w b u)*(d1_2_0 y z w b u))+0)+((d0_21_1 y z w b u)*(d1_1_1 y z w b u))))+(((d2_5_1 y z w b u)*(d3_17_1 y z w b u))+((d2_6_0 y z w b u)*(d3_16_2 y z w b u))))+((-1)*(d4_22_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_19_2,d0_20_2,d0_21_1,d1_1_1,d1_2_0,d1_3_0,d2_5_1,d2_6_0,d3_16_2,d3_17_1,d4_22_2]
  ring
#print axioms coefficient_22_2

compact_certificate_declaration theorem coefficient_22_3 (y z w b u : ℂ) :
    (innerCertificate22 y z w b u)[3]?=some 0 := by
  change some (((((d0_19_3 y z w b u)*(d1_3_0 y z w b u))+0)+((-1)*(d4_22_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_19_3,d1_3_0,d4_22_3]
  ring
#print axioms coefficient_22_3

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_23 (y z w b u : ℂ) : (innerCertificate23 y z w b u).length=3 := by
  norm_num [innerCertificate23,add,multiply,scale,inner0_20,inner0_21,inner1_2,inner1_3,inner2_6,inner3_17,inner4_23]
compact_certificate_declaration theorem inner_eval_23 (y z w a b u : ℂ) :
    evaluate a (innerCertificate23 y z w b u)=(((((c0_20 y z w a b u)*(c1_3 y z w a b u))+((c0_21 y z w a b u)*(c1_2 y z w a b u)))+((c2_6 y z w a b u)*(c3_17 y z w a b u)))+((-1)*(c4_23 y z w a b u))) := by
  simp only [innerCertificate23,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_20,c0_21,c1_2,c1_3,c2_6,c3_17,c4_23]
#print axioms inner_eval_23

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem coefficient_23_0 (y z w b u : ℂ) :
    (innerCertificate23 y z w b u)[0]?=some 0 := by
  change some (((((((d0_20_0 y z w b u)*(d1_3_0 y z w b u))+0)+(((d0_21_0 y z w b u)*(d1_2_0 y z w b u))+0))+(((d2_6_0 y z w b u)*(d3_17_0 y z w b u))+0))+(((-1)*(d4_23_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_20_0,d0_21_0,d1_2_0,d1_3_0,d2_6_0,d3_17_0,d4_23_0]
  ring
#print axioms coefficient_23_0
compact_certificate_declaration theorem coefficient_23_1 (y z w b u : ℂ) :
    (innerCertificate23 y z w b u)[1]?=some 0 := by
  change some (((((((d0_20_1 y z w b u)*(d1_3_0 y z w b u))+0)+(((d0_21_1 y z w b u)*(d1_2_0 y z w b u))+0))+((d2_6_0 y z w b u)*(d3_17_1 y z w b u)))+((-1)*(d4_23_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_20_1,d0_21_1,d1_2_0,d1_3_0,d2_6_0,d3_17_1,d4_23_1]
  ring
#print axioms coefficient_23_1
compact_certificate_declaration theorem coefficient_23_2 (y z w b u : ℂ) :
    (innerCertificate23 y z w b u)[2]?=some 0 := by
  change some (((((d0_20_2 y z w b u)*(d1_3_0 y z w b u))+0)+((-1)*(d4_23_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_20_2,d1_3_0,d4_23_2]
  ring
#print axioms coefficient_23_2

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_24 (y z w b u : ℂ) : (innerCertificate24 y z w b u).length=2 := by
  norm_num [innerCertificate24,add,multiply,scale,inner0_21,inner1_3,inner4_24]
compact_certificate_declaration theorem inner_eval_24 (y z w a b u : ℂ) :
    evaluate a (innerCertificate24 y z w b u)=(((c0_21 y z w a b u)*(c1_3 y z w a b u))+((-1)*(c4_24 y z w a b u))) := by
  simp only [innerCertificate24,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_21,c1_3,c4_24]
#print axioms inner_eval_24

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem coefficient_24_0 (y z w b u : ℂ) :
    (innerCertificate24 y z w b u)[0]?=some 0 := by
  change some (((((d0_21_0 y z w b u)*(d1_3_0 y z w b u))+0)+(((-1)*(d4_24_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_21_0,d1_3_0,d4_24_0]
  ring
#print axioms coefficient_24_0
compact_certificate_declaration theorem coefficient_24_1 (y z w b u : ℂ) :
    (innerCertificate24 y z w b u)[1]?=some 0 := by
  change some (((((d0_21_1 y z w b u)*(d1_3_0 y z w b u))+0)+((-1)*(d4_24_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_21_1,d1_3_0,d4_24_1]
  ring
#print axioms coefficient_24_1

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem inner_zero_0 (y z w b u : ℂ) : ∀ v∈innerCertificate0 y z w b u,v=0 := by
  apply zero_of_getElem? _ 10 (inner_length_0 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_0_0 y z w b u
  · exact coefficient_0_1 y z w b u
  · exact coefficient_0_2 y z w b u
  · exact coefficient_0_3 y z w b u
  · exact coefficient_0_4 y z w b u
  · exact coefficient_0_5 y z w b u
  · exact coefficient_0_6 y z w b u
  · exact coefficient_0_7 y z w b u
  · exact coefficient_0_8 y z w b u
  · exact coefficient_0_9 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 0 through 0 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_1 (y z w b u : ℂ) : ∀ v∈innerCertificate1 y z w b u,v=0 := by
  apply zero_of_getElem? _ 12 (inner_length_1 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_1_0 y z w b u
  · exact coefficient_1_1 y z w b u
  · exact coefficient_1_2 y z w b u
  · exact coefficient_1_3 y z w b u
  · exact coefficient_1_4 y z w b u
  · exact coefficient_1_5 y z w b u
  · exact coefficient_1_6 y z w b u
  · exact coefficient_1_7 y z w b u
  · exact coefficient_1_8 y z w b u
  · exact coefficient_1_9 y z w b u
  · exact coefficient_1_10 y z w b u
  · exact coefficient_1_11 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 1 through 1 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_2 (y z w b u : ℂ) : ∀ v∈innerCertificate2 y z w b u,v=0 := by
  apply zero_of_getElem? _ 12 (inner_length_2 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_2_0 y z w b u
  · exact coefficient_2_1 y z w b u
  · exact coefficient_2_2 y z w b u
  · exact coefficient_2_3 y z w b u
  · exact coefficient_2_4 y z w b u
  · exact coefficient_2_5 y z w b u
  · exact coefficient_2_6 y z w b u
  · exact coefficient_2_7 y z w b u
  · exact coefficient_2_8 y z w b u
  · exact coefficient_2_9 y z w b u
  · exact coefficient_2_10 y z w b u
  · exact coefficient_2_11 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 2 through 2 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_3 (y z w b u : ℂ) : ∀ v∈innerCertificate3 y z w b u,v=0 := by
  apply zero_of_getElem? _ 12 (inner_length_3 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_3_0 y z w b u
  · exact coefficient_3_1 y z w b u
  · exact coefficient_3_2 y z w b u
  · exact coefficient_3_3 y z w b u
  · exact coefficient_3_4 y z w b u
  · exact coefficient_3_5 y z w b u
  · exact coefficient_3_6 y z w b u
  · exact coefficient_3_7 y z w b u
  · exact coefficient_3_8 y z w b u
  · exact coefficient_3_9 y z w b u
  · exact coefficient_3_10 y z w b u
  · exact coefficient_3_11 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 3 through 3 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_4 (y z w b u : ℂ) : ∀ v∈innerCertificate4 y z w b u,v=0 := by
  apply zero_of_getElem? _ 12 (inner_length_4 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_4_0 y z w b u
  · exact coefficient_4_1 y z w b u
  · exact coefficient_4_2 y z w b u
  · exact coefficient_4_3 y z w b u
  · exact coefficient_4_4 y z w b u
  · exact coefficient_4_5 y z w b u
  · exact coefficient_4_6 y z w b u
  · exact coefficient_4_7 y z w b u
  · exact coefficient_4_8 y z w b u
  · exact coefficient_4_9 y z w b u
  · exact coefficient_4_10 y z w b u
  · exact coefficient_4_11 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 4 through 4 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_5 (y z w b u : ℂ) : ∀ v∈innerCertificate5 y z w b u,v=0 := by
  apply zero_of_getElem? _ 12 (inner_length_5 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_5_0 y z w b u
  · exact coefficient_5_1 y z w b u
  · exact coefficient_5_2 y z w b u
  · exact coefficient_5_3 y z w b u
  · exact coefficient_5_4 y z w b u
  · exact coefficient_5_5 y z w b u
  · exact coefficient_5_6 y z w b u
  · exact coefficient_5_7 y z w b u
  · exact coefficient_5_8 y z w b u
  · exact coefficient_5_9 y z w b u
  · exact coefficient_5_10 y z w b u
  · exact coefficient_5_11 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 5 through 5 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_6 (y z w b u : ℂ) : ∀ v∈innerCertificate6 y z w b u,v=0 := by
  apply zero_of_getElem? _ 12 (inner_length_6 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_6_0 y z w b u
  · exact coefficient_6_1 y z w b u
  · exact coefficient_6_2 y z w b u
  · exact coefficient_6_3 y z w b u
  · exact coefficient_6_4 y z w b u
  · exact coefficient_6_5 y z w b u
  · exact coefficient_6_6 y z w b u
  · exact coefficient_6_7 y z w b u
  · exact coefficient_6_8 y z w b u
  · exact coefficient_6_9 y z w b u
  · exact coefficient_6_10 y z w b u
  · exact coefficient_6_11 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 6 through 6 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_7 (y z w b u : ℂ) : ∀ v∈innerCertificate7 y z w b u,v=0 := by
  apply zero_of_getElem? _ 12 (inner_length_7 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_7_0 y z w b u
  · exact coefficient_7_1 y z w b u
  · exact coefficient_7_2 y z w b u
  · exact coefficient_7_3 y z w b u
  · exact coefficient_7_4 y z w b u
  · exact coefficient_7_5 y z w b u
  · exact coefficient_7_6 y z w b u
  · exact coefficient_7_7 y z w b u
  · exact coefficient_7_8 y z w b u
  · exact coefficient_7_9 y z w b u
  · exact coefficient_7_10 y z w b u
  · exact coefficient_7_11 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 7 through 7 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_8 (y z w b u : ℂ) : ∀ v∈innerCertificate8 y z w b u,v=0 := by
  apply zero_of_getElem? _ 12 (inner_length_8 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_8_0 y z w b u
  · exact coefficient_8_1 y z w b u
  · exact coefficient_8_2 y z w b u
  · exact coefficient_8_3 y z w b u
  · exact coefficient_8_4 y z w b u
  · exact coefficient_8_5 y z w b u
  · exact coefficient_8_6 y z w b u
  · exact coefficient_8_7 y z w b u
  · exact coefficient_8_8 y z w b u
  · exact coefficient_8_9 y z w b u
  · exact coefficient_8_10 y z w b u
  · exact coefficient_8_11 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 8 through 8 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_9 (y z w b u : ℂ) : ∀ v∈innerCertificate9 y z w b u,v=0 := by
  apply zero_of_getElem? _ 12 (inner_length_9 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_9_0 y z w b u
  · exact coefficient_9_1 y z w b u
  · exact coefficient_9_2 y z w b u
  · exact coefficient_9_3 y z w b u
  · exact coefficient_9_4 y z w b u
  · exact coefficient_9_5 y z w b u
  · exact coefficient_9_6 y z w b u
  · exact coefficient_9_7 y z w b u
  · exact coefficient_9_8 y z w b u
  · exact coefficient_9_9 y z w b u
  · exact coefficient_9_10 y z w b u
  · exact coefficient_9_11 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 9 through 9 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_10 (y z w b u : ℂ) : ∀ v∈innerCertificate10 y z w b u,v=0 := by
  apply zero_of_getElem? _ 11 (inner_length_10 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_10_0 y z w b u
  · exact coefficient_10_1 y z w b u
  · exact coefficient_10_2 y z w b u
  · exact coefficient_10_3 y z w b u
  · exact coefficient_10_4 y z w b u
  · exact coefficient_10_5 y z w b u
  · exact coefficient_10_6 y z w b u
  · exact coefficient_10_7 y z w b u
  · exact coefficient_10_8 y z w b u
  · exact coefficient_10_9 y z w b u
  · exact coefficient_10_10 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 10 through 10 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_11 (y z w b u : ℂ) : ∀ v∈innerCertificate11 y z w b u,v=0 := by
  apply zero_of_getElem? _ 11 (inner_length_11 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_11_0 y z w b u
  · exact coefficient_11_1 y z w b u
  · exact coefficient_11_2 y z w b u
  · exact coefficient_11_3 y z w b u
  · exact coefficient_11_4 y z w b u
  · exact coefficient_11_5 y z w b u
  · exact coefficient_11_6 y z w b u
  · exact coefficient_11_7 y z w b u
  · exact coefficient_11_8 y z w b u
  · exact coefficient_11_9 y z w b u
  · exact coefficient_11_10 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 11 through 11 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_12 (y z w b u : ℂ) : ∀ v∈innerCertificate12 y z w b u,v=0 := by
  apply zero_of_getElem? _ 11 (inner_length_12 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_12_0 y z w b u
  · exact coefficient_12_1 y z w b u
  · exact coefficient_12_2 y z w b u
  · exact coefficient_12_3 y z w b u
  · exact coefficient_12_4 y z w b u
  · exact coefficient_12_5 y z w b u
  · exact coefficient_12_6 y z w b u
  · exact coefficient_12_7 y z w b u
  · exact coefficient_12_8 y z w b u
  · exact coefficient_12_9 y z w b u
  · exact coefficient_12_10 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 12 through 12 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_13 (y z w b u : ℂ) : ∀ v∈innerCertificate13 y z w b u,v=0 := by
  apply zero_of_getElem? _ 10 (inner_length_13 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_13_0 y z w b u
  · exact coefficient_13_1 y z w b u
  · exact coefficient_13_2 y z w b u
  · exact coefficient_13_3 y z w b u
  · exact coefficient_13_4 y z w b u
  · exact coefficient_13_5 y z w b u
  · exact coefficient_13_6 y z w b u
  · exact coefficient_13_7 y z w b u
  · exact coefficient_13_8 y z w b u
  · exact coefficient_13_9 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 13 through 13 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_14 (y z w b u : ℂ) : ∀ v∈innerCertificate14 y z w b u,v=0 := by
  apply zero_of_getElem? _ 10 (inner_length_14 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_14_0 y z w b u
  · exact coefficient_14_1 y z w b u
  · exact coefficient_14_2 y z w b u
  · exact coefficient_14_3 y z w b u
  · exact coefficient_14_4 y z w b u
  · exact coefficient_14_5 y z w b u
  · exact coefficient_14_6 y z w b u
  · exact coefficient_14_7 y z w b u
  · exact coefficient_14_8 y z w b u
  · exact coefficient_14_9 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 14 through 14 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_15 (y z w b u : ℂ) : ∀ v∈innerCertificate15 y z w b u,v=0 := by
  apply zero_of_getElem? _ 9 (inner_length_15 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_15_0 y z w b u
  · exact coefficient_15_1 y z w b u
  · exact coefficient_15_2 y z w b u
  · exact coefficient_15_3 y z w b u
  · exact coefficient_15_4 y z w b u
  · exact coefficient_15_5 y z w b u
  · exact coefficient_15_6 y z w b u
  · exact coefficient_15_7 y z w b u
  · exact coefficient_15_8 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 15 through 15 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_16 (y z w b u : ℂ) : ∀ v∈innerCertificate16 y z w b u,v=0 := by
  apply zero_of_getElem? _ 8 (inner_length_16 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_16_0 y z w b u
  · exact coefficient_16_1 y z w b u
  · exact coefficient_16_2 y z w b u
  · exact coefficient_16_3 y z w b u
  · exact coefficient_16_4 y z w b u
  · exact coefficient_16_5 y z w b u
  · exact coefficient_16_6 y z w b u
  · exact coefficient_16_7 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 16 through 16 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_17 (y z w b u : ℂ) : ∀ v∈innerCertificate17 y z w b u,v=0 := by
  apply zero_of_getElem? _ 8 (inner_length_17 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_17_0 y z w b u
  · exact coefficient_17_1 y z w b u
  · exact coefficient_17_2 y z w b u
  · exact coefficient_17_3 y z w b u
  · exact coefficient_17_4 y z w b u
  · exact coefficient_17_5 y z w b u
  · exact coefficient_17_6 y z w b u
  · exact coefficient_17_7 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 17 through 17 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_18 (y z w b u : ℂ) : ∀ v∈innerCertificate18 y z w b u,v=0 := by
  apply zero_of_getElem? _ 7 (inner_length_18 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_18_0 y z w b u
  · exact coefficient_18_1 y z w b u
  · exact coefficient_18_2 y z w b u
  · exact coefficient_18_3 y z w b u
  · exact coefficient_18_4 y z w b u
  · exact coefficient_18_5 y z w b u
  · exact coefficient_18_6 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 18 through 18 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_19 (y z w b u : ℂ) : ∀ v∈innerCertificate19 y z w b u,v=0 := by
  apply zero_of_getElem? _ 7 (inner_length_19 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_19_0 y z w b u
  · exact coefficient_19_1 y z w b u
  · exact coefficient_19_2 y z w b u
  · exact coefficient_19_3 y z w b u
  · exact coefficient_19_4 y z w b u
  · exact coefficient_19_5 y z w b u
  · exact coefficient_19_6 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 19 through 19 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_20 (y z w b u : ℂ) : ∀ v∈innerCertificate20 y z w b u,v=0 := by
  apply zero_of_getElem? _ 6 (inner_length_20 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_20_0 y z w b u
  · exact coefficient_20_1 y z w b u
  · exact coefficient_20_2 y z w b u
  · exact coefficient_20_3 y z w b u
  · exact coefficient_20_4 y z w b u
  · exact coefficient_20_5 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 20 through 20 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_21 (y z w b u : ℂ) : ∀ v∈innerCertificate21 y z w b u,v=0 := by
  apply zero_of_getElem? _ 5 (inner_length_21 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_21_0 y z w b u
  · exact coefficient_21_1 y z w b u
  · exact coefficient_21_2 y z w b u
  · exact coefficient_21_3 y z w b u
  · exact coefficient_21_4 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 21 through 21 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_22 (y z w b u : ℂ) : ∀ v∈innerCertificate22 y z w b u,v=0 := by
  apply zero_of_getElem? _ 4 (inner_length_22 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_22_0 y z w b u
  · exact coefficient_22_1 y z w b u
  · exact coefficient_22_2 y z w b u
  · exact coefficient_22_3 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 22 through 22 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_23 (y z w b u : ℂ) : ∀ v∈innerCertificate23 y z w b u,v=0 := by
  apply zero_of_getElem? _ 3 (inner_length_23 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_23_0 y z w b u
  · exact coefficient_23_1 y z w b u
  · exact coefficient_23_2 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 23 through 23 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_24 (y z w b u : ℂ) : ∀ v∈innerCertificate24 y z w b u,v=0 := by
  apply zero_of_getElem? _ 2 (inner_length_24 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_24_0 y z w b u
  · exact coefficient_24_1 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 24 through 24 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, coefficients4, coefficients5, coefficients6, certificate]

end SmallLevelTwentySixMMPPariTrace014
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace014
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_zero (y z w a b u : ℂ) : ∀ v∈certificate y z w a b u,v=0 := by
  apply zero_of_getElem? _ 25 (certificate_length y z w a b u)
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
compact_certificate_declaration theorem identity (x y z w a b u : ℂ) :
    p0 x y z w a b u*p1 x y z w a b u+p2 x y z w a b u*p3 x y z w a b u=p4 x y z w a b u+p5 x y z w a b u*p6 x y z w a b u := by
  unfold p0 p1 p2 p3 p4 p5 p6
  exact of_zero_coefficients x _ _ _ _ _ _ _ (certificate_zero y z w a b u)
#print axioms identity

end SmallLevelTwentySixMMPPariTrace014
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

namespace SmallLevelTwentySixMMPPariTrace015
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_length (y z w a b u : ℂ) : (certificate y z w a b u).length=25 := by
  norm_num [certificate,add,multiply,scale,coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6]

end SmallLevelTwentySixMMPPariTrace015
end

section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

namespace SmallLevelTwentySixMMPPariTrace015
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem identity_shift (x y z w a b u : ℂ) :
    p0 x y z w a b u*p1 x y z w a b u+p2 x y z w a b u*p3 x y z w a b u=
      p4 x y z w a b u+p5 x y z w a b u*p6 x y z w a b u := by
  have h0 : p0 x y z w a b u=1 := by norm_num [p0,coefficients0,c0_0,evaluate]
  have h2 : p2 x y z w a b u=0 := by norm_num [p2,coefficients2,evaluate]
  have h4 : p4 x y z w a b u=0 := by norm_num [p4,coefficients4,evaluate]
  have h5 : p5 x y z w a b u=x^3 := by
    simp only [p5,coefficients5,c5_0,c5_1,c5_2,c5_3,evaluate]
    ring
  have hcoeff : coefficients1 y z w a b u=List.replicate 3 0 ++ coefficients6 y z w a b u := by rfl
  rw [h0,h2,h4,h5]
  simp only [one_mul,zero_mul,zero_add,add_zero]
  unfold p1 p6
  rw [hcoeff]
  exact SmallLevelPolynomialZeroPrefix.evaluate_zero_prefix x _ _
#print axioms identity_shift
end SmallLevelTwentySixMMPPariTrace015
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

namespace SmallLevelTwentySixMMPPariTrace016
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_length (y z w a b u : ℂ) : (certificate y z w a b u).length=33 := by
  norm_num [certificate,add,multiply,scale,coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6]

end SmallLevelTwentySixMMPPariTrace016
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace016
open SmallLevelPolynomialCoefficientCertificate

certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 0 through 32 unfolding [c0_0, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, c1_6, c1_7, c1_8, c1_9, c1_10, c1_11, c1_12, c1_13, c1_14, c1_15, c1_16, c1_17, c1_18, c1_19, c1_20, c1_21, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, c2_11, c2_12, c2_13, c2_14, c2_15, c2_16, c2_17, c2_18, c2_19, c2_20, c2_21, c2_22, c2_23, c2_24, c2_25, c2_26, c2_27, c2_28, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, c4_32, coefficients4, coefficients5, coefficients6, certificate]

end SmallLevelTwentySixMMPPariTrace016
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace016
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

end SmallLevelTwentySixMMPPariTrace016
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

namespace SmallLevelTwentySixMMPPariTrace017
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_length (y z w a b u : ℂ) : (certificate y z w a b u).length=38 := by
  norm_num [certificate,add,multiply,scale,coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6]

end SmallLevelTwentySixMMPPariTrace017
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace017
open SmallLevelPolynomialCoefficientCertificate

certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 0 through 37 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, c0_29, c0_30, c0_31, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, c1_6, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, c3_20, c3_21, c3_22, c3_23, c3_24, c3_25, c3_26, c3_27, c3_28, c3_29, c3_30, c3_31, c3_32, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, c4_32, c4_33, c4_34, c4_35, coefficients4, coefficients5, coefficients6, certificate]

end SmallLevelTwentySixMMPPariTrace017
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace017
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_zero (y z w a b u : ℂ) : ∀ v∈certificate y z w a b u,v=0 := by
  apply zero_of_getElem? _ 38 (certificate_length y z w a b u)
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
compact_certificate_declaration theorem identity (x y z w a b u : ℂ) :
    p0 x y z w a b u*p1 x y z w a b u+p2 x y z w a b u*p3 x y z w a b u=
      p4 x y z w a b u+p5 x y z w a b u*p6 x y z w a b u := by
  unfold p0 p1 p2 p3 p4 p5 p6
  exact of_zero_coefficients x _ _ _ _ _ _ _ (certificate_zero y z w a b u)
#print axioms identity

end SmallLevelTwentySixMMPPariTrace017
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

namespace SmallLevelTwentySixMMPPariTrace018
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_length (y z w a b u : ℂ) : (certificate y z w a b u).length=36 := by
  norm_num [certificate,add,multiply,scale,coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6]

end SmallLevelTwentySixMMPPariTrace018
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace018
open SmallLevelPolynomialCoefficientCertificate

certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 0 through 35 unfolding [c0_0, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, c1_6, c1_7, c1_8, c1_9, c1_10, c1_11, c1_12, c1_13, c1_14, c1_15, c1_16, c1_17, c1_18, c1_19, c1_20, c1_21, c1_22, c1_23, c1_24, c1_25, c1_26, c1_27, c1_28, c1_29, c1_30, c1_31, c1_32, c1_33, c1_34, c1_35, coefficients1, coefficients2, coefficients3, coefficients4, c5_0, c5_1, c5_2, c5_3, coefficients5, c6_0, c6_1, c6_2, c6_3, c6_4, c6_5, c6_6, c6_7, c6_8, c6_9, c6_10, c6_11, c6_12, c6_13, c6_14, c6_15, c6_16, c6_17, c6_18, c6_19, c6_20, c6_21, c6_22, c6_23, c6_24, c6_25, c6_26, c6_27, c6_28, c6_29, c6_30, c6_31, c6_32, coefficients6, certificate]

end SmallLevelTwentySixMMPPariTrace018
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace018
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_zero (y z w a b u : ℂ) : ∀ v∈certificate y z w a b u,v=0 := by
  apply zero_of_getElem? _ 36 (certificate_length y z w a b u)
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
compact_certificate_declaration theorem identity (x y z w a b u : ℂ) :
    p0 x y z w a b u*p1 x y z w a b u+p2 x y z w a b u*p3 x y z w a b u=
      p4 x y z w a b u+p5 x y z w a b u*p6 x y z w a b u := by
  unfold p0 p1 p2 p3 p4 p5 p6
  exact of_zero_coefficients x _ _ _ _ _ _ _ (certificate_zero y z w a b u)
#print axioms identity

end SmallLevelTwentySixMMPPariTrace018
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

namespace SmallLevelTwentySixMMPPariTrace020
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_length (y z w a b u : ℂ) : (certificate y z w a b u).length=133 := by
  norm_num [certificate,add,multiply,scale,coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6]

end SmallLevelTwentySixMMPPariTrace020
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace020
open SmallLevelPolynomialCoefficientCertificate

certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 0 through 132 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, c0_29, c0_30, c0_31, c0_32, c0_33, c0_34, c0_35, c0_36, c0_37, c0_38, c0_39, c0_40, c0_41, c0_42, c0_43, c0_44, c0_45, c0_46, c0_47, c0_48, c0_49, c0_50, c0_51, c0_52, c0_53, c0_54, c0_55, c0_56, c0_57, c0_58, c0_59, c0_60, c0_61, c0_62, c0_63, c0_64, c0_65, c0_66, c0_67, c0_68, c0_69, c0_70, c0_71, c0_72, c0_73, c0_74, c0_75, c0_76, c0_77, c0_78, c0_79, c0_80, c0_81, c0_82, c0_83, c0_84, c0_85, c0_86, c0_87, c0_88, c0_89, c0_90, c0_91, c0_92, c0_93, c0_94, c0_95, c0_96, c0_97, c0_98, c0_99, c0_100, c0_101, c0_102, c0_103, c0_104, c0_105, c0_106, c0_107, c0_108, c0_109, c0_110, c0_111, c0_112, c0_113, c0_114, c0_115, c0_116, c0_117, c0_118, c0_119, c0_120, c0_121, c0_122, c0_123, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, c1_6, c1_7, c1_8, c1_9, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, c2_11, c2_12, c2_13, c2_14, c2_15, c2_16, c2_17, c2_18, c2_19, c2_20, c2_21, c2_22, c2_23, c2_24, c2_25, c2_26, c2_27, c2_28, c2_29, c2_30, c2_31, c2_32, c2_33, c2_34, c2_35, c2_36, c2_37, c2_38, c2_39, c2_40, c2_41, c2_42, c2_43, c2_44, c2_45, c2_46, c2_47, c2_48, c2_49, c2_50, c2_51, c2_52, c2_53, c2_54, c2_55, c2_56, c2_57, c2_58, c2_59, c2_60, c2_61, c2_62, c2_63, c2_64, c2_65, c2_66, c2_67, c2_68, c2_69, c2_70, c2_71, c2_72, c2_73, c2_74, c2_75, c2_76, c2_77, c2_78, c2_79, c2_80, c2_81, c2_82, c2_83, c2_84, c2_85, c2_86, c2_87, c2_88, c2_89, c2_90, c2_91, c2_92, c2_93, c2_94, c2_95, c2_96, c2_97, c2_98, c2_99, c2_100, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, c3_20, c3_21, c3_22, c3_23, c3_24, c3_25, c3_26, c3_27, c3_28, c3_29, c3_30, c3_31, c3_32, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, c4_32, c4_33, c4_34, c4_35, c4_36, c4_37, c4_38, c4_39, c4_40, c4_41, c4_42, c4_43, c4_44, c4_45, c4_46, c4_47, c4_48, c4_49, c4_50, c4_51, c4_52, c4_53, c4_54, c4_55, c4_56, c4_57, c4_58, c4_59, c4_60, c4_61, c4_62, c4_63, c4_64, c4_65, c4_66, c4_67, c4_68, c4_69, c4_70, c4_71, c4_72, c4_73, c4_74, c4_75, c4_76, c4_77, c4_78, c4_79, c4_80, c4_81, c4_82, c4_83, c4_84, c4_85, c4_86, c4_87, c4_88, c4_89, c4_90, c4_91, c4_92, c4_93, c4_94, c4_95, c4_96, c4_97, c4_98, c4_99, c4_100, c4_101, c4_102, c4_103, c4_104, c4_105, c4_106, c4_107, c4_108, c4_109, c4_110, c4_111, c4_112, c4_113, c4_114, c4_115, c4_116, c4_117, c4_118, c4_119, c4_120, c4_121, c4_122, c4_123, coefficients4, coefficients5, coefficients6, certificate]

end SmallLevelTwentySixMMPPariTrace020
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace020
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_zero (y z w a b u : ℂ) : ∀ v∈certificate y z w a b u,v=0 := by
  apply zero_of_getElem? _ 133 (certificate_length y z w a b u)
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
  · exact coefficient_41 y z w a b u
  · exact coefficient_42 y z w a b u
  · exact coefficient_43 y z w a b u
  · exact coefficient_44 y z w a b u
  · exact coefficient_45 y z w a b u
  · exact coefficient_46 y z w a b u
  · exact coefficient_47 y z w a b u
  · exact coefficient_48 y z w a b u
  · exact coefficient_49 y z w a b u
  · exact coefficient_50 y z w a b u
  · exact coefficient_51 y z w a b u
  · exact coefficient_52 y z w a b u
  · exact coefficient_53 y z w a b u
  · exact coefficient_54 y z w a b u
  · exact coefficient_55 y z w a b u
  · exact coefficient_56 y z w a b u
  · exact coefficient_57 y z w a b u
  · exact coefficient_58 y z w a b u
  · exact coefficient_59 y z w a b u
  · exact coefficient_60 y z w a b u
  · exact coefficient_61 y z w a b u
  · exact coefficient_62 y z w a b u
  · exact coefficient_63 y z w a b u
  · exact coefficient_64 y z w a b u
  · exact coefficient_65 y z w a b u
  · exact coefficient_66 y z w a b u
  · exact coefficient_67 y z w a b u
  · exact coefficient_68 y z w a b u
  · exact coefficient_69 y z w a b u
  · exact coefficient_70 y z w a b u
  · exact coefficient_71 y z w a b u
  · exact coefficient_72 y z w a b u
  · exact coefficient_73 y z w a b u
  · exact coefficient_74 y z w a b u
  · exact coefficient_75 y z w a b u
  · exact coefficient_76 y z w a b u
  · exact coefficient_77 y z w a b u
  · exact coefficient_78 y z w a b u
  · exact coefficient_79 y z w a b u
  · exact coefficient_80 y z w a b u
  · exact coefficient_81 y z w a b u
  · exact coefficient_82 y z w a b u
  · exact coefficient_83 y z w a b u
  · exact coefficient_84 y z w a b u
  · exact coefficient_85 y z w a b u
  · exact coefficient_86 y z w a b u
  · exact coefficient_87 y z w a b u
  · exact coefficient_88 y z w a b u
  · exact coefficient_89 y z w a b u
  · exact coefficient_90 y z w a b u
  · exact coefficient_91 y z w a b u
  · exact coefficient_92 y z w a b u
  · exact coefficient_93 y z w a b u
  · exact coefficient_94 y z w a b u
  · exact coefficient_95 y z w a b u
  · exact coefficient_96 y z w a b u
  · exact coefficient_97 y z w a b u
  · exact coefficient_98 y z w a b u
  · exact coefficient_99 y z w a b u
  · exact coefficient_100 y z w a b u
  · exact coefficient_101 y z w a b u
  · exact coefficient_102 y z w a b u
  · exact coefficient_103 y z w a b u
  · exact coefficient_104 y z w a b u
  · exact coefficient_105 y z w a b u
  · exact coefficient_106 y z w a b u
  · exact coefficient_107 y z w a b u
  · exact coefficient_108 y z w a b u
  · exact coefficient_109 y z w a b u
  · exact coefficient_110 y z w a b u
  · exact coefficient_111 y z w a b u
  · exact coefficient_112 y z w a b u
  · exact coefficient_113 y z w a b u
  · exact coefficient_114 y z w a b u
  · exact coefficient_115 y z w a b u
  · exact coefficient_116 y z w a b u
  · exact coefficient_117 y z w a b u
  · exact coefficient_118 y z w a b u
  · exact coefficient_119 y z w a b u
  · exact coefficient_120 y z w a b u
  · exact coefficient_121 y z w a b u
  · exact coefficient_122 y z w a b u
  · exact coefficient_123 y z w a b u
  · exact coefficient_124 y z w a b u
  · exact coefficient_125 y z w a b u
  · exact coefficient_126 y z w a b u
  · exact coefficient_127 y z w a b u
  · exact coefficient_128 y z w a b u
  · exact coefficient_129 y z w a b u
  · exact coefficient_130 y z w a b u
  · exact coefficient_131 y z w a b u
  · exact coefficient_132 y z w a b u
compact_certificate_declaration theorem identity (x y z w a b u : ℂ) :
    p0 x y z w a b u*p1 x y z w a b u+p2 x y z w a b u*p3 x y z w a b u=
      p4 x y z w a b u+p5 x y z w a b u*p6 x y z w a b u := by
  unfold p0 p1 p2 p3 p4 p5 p6
  exact of_zero_coefficients x _ _ _ _ _ _ _ (certificate_zero y z w a b u)
#print axioms identity

end SmallLevelTwentySixMMPPariTrace020
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

namespace SmallLevelTwentySixMMPPariTrace022
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_length (y z w a b u : ℂ) : (certificate y z w a b u).length=17 := by
  norm_num [certificate,add,multiply,scale,coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6]

end SmallLevelTwentySixMMPPariTrace022
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace022
open SmallLevelPolynomialCoefficientCertificate

certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 0 through 16 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, coefficients0, c1_0, c1_1, c1_2, coefficients1, c2_0, c2_1, c2_2, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, coefficients4, coefficients5, coefficients6, certificate]

end SmallLevelTwentySixMMPPariTrace022
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace022
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_zero (y z w a b u : ℂ) : ∀ v∈certificate y z w a b u,v=0 := by
  apply zero_of_getElem? _ 17 (certificate_length y z w a b u)
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
compact_certificate_declaration theorem identity (x y z w a b u : ℂ) :
    p0 x y z w a b u*p1 x y z w a b u+p2 x y z w a b u*p3 x y z w a b u=
      p4 x y z w a b u+p5 x y z w a b u*p6 x y z w a b u := by
  unfold p0 p1 p2 p3 p4 p5 p6
  exact of_zero_coefficients x _ _ _ _ _ _ _ (certificate_zero y z w a b u)
#print axioms identity

end SmallLevelTwentySixMMPPariTrace022
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

namespace SmallLevelTwentySixMMPPariTrace023
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_length (y z w a b u : ℂ) : (certificate y z w a b u).length=17 := by
  norm_num [certificate,add,multiply,scale,coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6]

end SmallLevelTwentySixMMPPariTrace023
end

section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

namespace SmallLevelTwentySixMMPPariTrace023
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem identity_shift (x y z w a b u : ℂ) :
    p0 x y z w a b u*p1 x y z w a b u+p2 x y z w a b u*p3 x y z w a b u=
      p4 x y z w a b u+p5 x y z w a b u*p6 x y z w a b u := by
  have h0 : p0 x y z w a b u=1 := by norm_num [p0,coefficients0,c0_0,evaluate]
  have h2 : p2 x y z w a b u=0 := by norm_num [p2,coefficients2,evaluate]
  have h4 : p4 x y z w a b u=0 := by norm_num [p4,coefficients4,evaluate]
  have h5 : p5 x y z w a b u=x^1 := by
    simp only [p5,coefficients5,c5_0,c5_1,evaluate]
    ring
  have hcoeff : coefficients1 y z w a b u=List.replicate 1 0 ++ coefficients6 y z w a b u := by rfl
  rw [h0,h2,h4,h5]
  simp only [one_mul,zero_mul,zero_add,add_zero]
  unfold p1 p6
  rw [hcoeff]
  exact SmallLevelPolynomialZeroPrefix.evaluate_zero_prefix x _ _
#print axioms identity_shift
end SmallLevelTwentySixMMPPariTrace023
end
end

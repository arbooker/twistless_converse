module
public import SmallLevelTwentySixMMPPariTraceFourteenV4
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

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_length (y z w a b u : ℂ) : (certificate y z w a b u).length=22 := by
  norm_num [certificate,add,multiply,scale,coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6]

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_0 (y z w b u : ℂ) : (innerCertificate0 y z w b u).length=1 := by
  norm_num [innerCertificate0,add,multiply,scale,inner0_0,inner1_0,inner2_0,inner3_0,inner4_0]
compact_certificate_declaration theorem inner_eval_0 (y z w a b u : ℂ) :
    evaluate a (innerCertificate0 y z w b u)=(((((c0_0 y z w a b u)*(c1_0 y z w a b u))+0)+(((c2_0 y z w a b u)*(c3_0 y z w a b u))+0))+((-1)*(c4_0 y z w a b u))) := by
  simp only [innerCertificate0,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_0,c1_0,c2_0,c3_0,c4_0]
#print axioms inner_eval_0

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem coefficient_0_0 (y z w b u : ℂ) :
    (innerCertificate0 y z w b u)[0]?=some 0 := by
  change some (0)=some (0:ℂ)
  apply congrArg some
  ring
#print axioms coefficient_0_0

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_1 (y z w b u : ℂ) : (innerCertificate1 y z w b u).length=1 := by
  norm_num [innerCertificate1,add,multiply,scale,inner0_0,inner0_1,inner1_0,inner1_1,inner2_0,inner2_1,inner3_0,inner3_1,inner4_1]
compact_certificate_declaration theorem inner_eval_1 (y z w a b u : ℂ) :
    evaluate a (innerCertificate1 y z w b u)=(((((c0_0 y z w a b u)*(c1_1 y z w a b u))+(((c0_1 y z w a b u)*(c1_0 y z w a b u))+0))+(((c2_0 y z w a b u)*(c3_1 y z w a b u))+(((c2_1 y z w a b u)*(c3_0 y z w a b u))+0)))+((-1)*(c4_1 y z w a b u))) := by
  simp only [innerCertificate1,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_0,c0_1,c1_0,c1_1,c2_0,c2_1,c3_0,c3_1,c4_1]
#print axioms inner_eval_1

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem coefficient_1_0 (y z w b u : ℂ) :
    (innerCertificate1 y z w b u)[0]?=some 0 := by
  change some (0)=some (0:ℂ)
  apply congrArg some
  ring
#print axioms coefficient_1_0

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_2 (y z w b u : ℂ) : (innerCertificate2 y z w b u).length=9 := by
  norm_num [innerCertificate2,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner1_0,inner1_1,inner1_2,inner2_0,inner2_1,inner2_2,inner3_0,inner3_1,inner3_2,inner4_2]
compact_certificate_declaration theorem inner_eval_2 (y z w a b u : ℂ) :
    evaluate a (innerCertificate2 y z w b u)=(((((c0_0 y z w a b u)*(c1_2 y z w a b u))+(((c0_1 y z w a b u)*(c1_1 y z w a b u))+(((c0_2 y z w a b u)*(c1_0 y z w a b u))+0)))+(((c2_0 y z w a b u)*(c3_2 y z w a b u))+(((c2_1 y z w a b u)*(c3_1 y z w a b u))+(((c2_2 y z w a b u)*(c3_0 y z w a b u))+0))))+((-1)*(c4_2 y z w a b u))) := by
  simp only [innerCertificate2,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_0,c0_1,c0_2,c1_0,c1_1,c1_2,c2_0,c2_1,c2_2,c3_0,c3_1,c3_2,c4_2]
#print axioms inner_eval_2

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_2_0 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[0]?=some 0 := by
  change some ((((((d0_2_0 y z w b u)*(d1_0_0 y z w b u))+0)+(((d2_2_0 y z w b u)*(d3_0_0 y z w b u))+0))+(((-1)*(d4_2_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_0,d1_0_0,d2_2_0,d3_0_0,d4_2_0]
  ring
#print axioms coefficient_2_0
compact_certificate_declaration theorem coefficient_2_1 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[1]?=some 0 := by
  change some ((((((d0_2_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_1 y z w b u)*(d1_0_0 y z w b u))+0))+(((d2_2_0 y z w b u)*(d3_0_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_0_0 y z w b u))+0)))+((-1)*(d4_2_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_0,d0_2_1,d1_0_0,d1_0_1,d2_2_0,d2_2_1,d3_0_0,d3_0_1,d4_2_1]
  ring
#print axioms coefficient_2_1
compact_certificate_declaration theorem coefficient_2_2 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[2]?=some 0 := by
  change some ((((((d0_2_0 y z w b u)*(d1_0_2 y z w b u))+(((d0_2_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_2 y z w b u)*(d1_0_0 y z w b u))+0)))+(((d2_2_0 y z w b u)*(d3_0_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_0_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_0_0 y z w b u))+0))))+((-1)*(d4_2_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_0,d0_2_1,d0_2_2,d1_0_0,d1_0_1,d1_0_2,d2_2_0,d2_2_1,d2_2_2,d3_0_0,d3_0_1,d3_0_2,d4_2_2]
  ring
#print axioms coefficient_2_2

compact_certificate_declaration theorem coefficient_2_3 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[3]?=some 0 := by
  change some ((((((d0_2_1 y z w b u)*(d1_0_2 y z w b u))+(((d0_2_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_3 y z w b u)*(d1_0_0 y z w b u))+0)))+(((d2_2_0 y z w b u)*(d3_0_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_0_2 y z w b u))+((d2_2_2 y z w b u)*(d3_0_1 y z w b u)))))+((-1)*(d4_2_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_1,d0_2_2,d0_2_3,d1_0_0,d1_0_1,d1_0_2,d2_2_0,d2_2_1,d2_2_2,d3_0_1,d3_0_2,d3_0_3,d4_2_3]
  ring
#print axioms coefficient_2_3
compact_certificate_declaration theorem coefficient_2_4 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[4]?=some 0 := by
  change some ((((((d0_2_2 y z w b u)*(d1_0_2 y z w b u))+(((d0_2_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_4 y z w b u)*(d1_0_0 y z w b u))+0)))+(((d2_2_0 y z w b u)*(d3_0_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_0_3 y z w b u))+((d2_2_2 y z w b u)*(d3_0_2 y z w b u)))))+((-1)*(d4_2_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_2,d0_2_3,d0_2_4,d1_0_0,d1_0_1,d1_0_2,d2_2_0,d2_2_1,d2_2_2,d3_0_2,d3_0_3,d3_0_4,d4_2_4]
  ring
#print axioms coefficient_2_4
compact_certificate_declaration theorem coefficient_2_5 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[5]?=some 0 := by
  change some ((((((d0_2_3 y z w b u)*(d1_0_2 y z w b u))+(((d0_2_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_5 y z w b u)*(d1_0_0 y z w b u))+0)))+(((d2_2_0 y z w b u)*(d3_0_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_0_4 y z w b u))+((d2_2_2 y z w b u)*(d3_0_3 y z w b u)))))+((-1)*(d4_2_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_3,d0_2_4,d0_2_5,d1_0_0,d1_0_1,d1_0_2,d2_2_0,d2_2_1,d2_2_2,d3_0_3,d3_0_4,d3_0_5,d4_2_5]
  ring
#print axioms coefficient_2_5

compact_certificate_declaration theorem coefficient_2_6 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[6]?=some 0 := by
  change some ((((((d0_2_4 y z w b u)*(d1_0_2 y z w b u))+(((d0_2_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_2_6 y z w b u)*(d1_0_0 y z w b u))+0)))+(((d2_2_0 y z w b u)*(d3_0_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_0_5 y z w b u))+((d2_2_2 y z w b u)*(d3_0_4 y z w b u)))))+((-1)*(d4_2_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_4,d0_2_5,d0_2_6,d1_0_0,d1_0_1,d1_0_2,d2_2_0,d2_2_1,d2_2_2,d3_0_4,d3_0_5,d3_0_6,d4_2_6]
  ring
#print axioms coefficient_2_6
compact_certificate_declaration theorem coefficient_2_7 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[7]?=some 0 := by
  change some ((((((d0_2_5 y z w b u)*(d1_0_2 y z w b u))+((d0_2_6 y z w b u)*(d1_0_1 y z w b u)))+(((d2_2_1 y z w b u)*(d3_0_6 y z w b u))+((d2_2_2 y z w b u)*(d3_0_5 y z w b u))))+((-1)*(d4_2_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_5,d0_2_6,d1_0_1,d1_0_2,d2_2_1,d2_2_2,d3_0_5,d3_0_6,d4_2_7]
  ring
#print axioms coefficient_2_7
compact_certificate_declaration theorem coefficient_2_8 (y z w b u : ℂ) :
    (innerCertificate2 y z w b u)[8]?=some 0 := by
  change some (((((d0_2_6 y z w b u)*(d1_0_2 y z w b u))+((d2_2_2 y z w b u)*(d3_0_6 y z w b u)))+((-1)*(d4_2_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_6,d1_0_2,d2_2_2,d3_0_6,d4_2_8]
  ring
#print axioms coefficient_2_8

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_3 (y z w b u : ℂ) : (innerCertificate3 y z w b u).length=10 := by
  norm_num [innerCertificate3,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner0_3,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner3_0,inner3_1,inner3_2,inner3_3,inner4_3]
compact_certificate_declaration theorem inner_eval_3 (y z w a b u : ℂ) :
    evaluate a (innerCertificate3 y z w b u)=(((((c0_0 y z w a b u)*(c1_3 y z w a b u))+(((c0_1 y z w a b u)*(c1_2 y z w a b u))+(((c0_2 y z w a b u)*(c1_1 y z w a b u))+(((c0_3 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_3 y z w a b u))+(((c2_1 y z w a b u)*(c3_2 y z w a b u))+(((c2_2 y z w a b u)*(c3_1 y z w a b u))+(((c2_3 y z w a b u)*(c3_0 y z w a b u))+0)))))+((-1)*(c4_3 y z w a b u))) := by
  simp only [innerCertificate3,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_0,c0_1,c0_2,c0_3,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c3_0,c3_1,c3_2,c3_3,c4_3]
#print axioms inner_eval_3

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_3_0 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[0]?=some 0 := by
  change some (((((((d0_2_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_3_0 y z w b u)*(d1_0_0 y z w b u))+0))+((((d2_2_0 y z w b u)*(d3_1_0 y z w b u))+0)+(((d2_3_0 y z w b u)*(d3_0_0 y z w b u))+0)))+(((-1)*(d4_3_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_0,d0_3_0,d1_0_0,d1_1_0,d2_2_0,d2_3_0,d3_0_0,d3_1_0,d4_3_0]
  ring
#print axioms coefficient_3_0
compact_certificate_declaration theorem coefficient_3_1 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[1]?=some 0 := by
  change some (((((((d0_2_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_3_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_1 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_1_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_0 y z w b u))+0))+(((d2_3_0 y z w b u)*(d3_0_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_0_0 y z w b u))+0))))+((-1)*(d4_3_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_0,d0_2_1,d0_3_0,d0_3_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d3_0_0,d3_0_1,d3_1_0,d3_1_1,d4_3_1]
  ring
#print axioms coefficient_3_1
compact_certificate_declaration theorem coefficient_3_2 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[2]?=some 0 := by
  change some (((((((d0_2_0 y z w b u)*(d1_1_2 y z w b u))+(((d0_2_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_2 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_3_0 y z w b u)*(d1_0_2 y z w b u))+(((d0_3_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_2 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_1_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_1_0 y z w b u))+0)))+(((d2_3_0 y z w b u)*(d3_0_2 y z w b u))+((d2_3_1 y z w b u)*(d3_0_1 y z w b u)))))+((-1)*(d4_3_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_0,d0_2_1,d0_2_2,d0_3_0,d0_3_1,d0_3_2,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d3_0_1,d3_0_2,d3_1_0,d3_1_1,d3_1_2,d4_3_2]
  ring
#print axioms coefficient_3_2

compact_certificate_declaration theorem coefficient_3_3 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[3]?=some 0 := by
  change some (((((((d0_2_1 y z w b u)*(d1_1_2 y z w b u))+(((d0_2_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_3 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_3_1 y z w b u)*(d1_0_2 y z w b u))+(((d0_3_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_3 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_1_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_2 y z w b u))+((d2_2_2 y z w b u)*(d3_1_1 y z w b u))))+(((d2_3_0 y z w b u)*(d3_0_3 y z w b u))+((d2_3_1 y z w b u)*(d3_0_2 y z w b u)))))+((-1)*(d4_3_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_1,d0_2_2,d0_2_3,d0_3_1,d0_3_2,d0_3_3,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d3_0_2,d3_0_3,d3_1_1,d3_1_2,d3_1_3,d4_3_3]
  ring
#print axioms coefficient_3_3
compact_certificate_declaration theorem coefficient_3_4 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[4]?=some 0 := by
  change some (((((((d0_2_2 y z w b u)*(d1_1_2 y z w b u))+(((d0_2_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_4 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_3_2 y z w b u)*(d1_0_2 y z w b u))+(((d0_3_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_4 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_1_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_3 y z w b u))+((d2_2_2 y z w b u)*(d3_1_2 y z w b u))))+(((d2_3_0 y z w b u)*(d3_0_4 y z w b u))+((d2_3_1 y z w b u)*(d3_0_3 y z w b u)))))+((-1)*(d4_3_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_2,d0_2_3,d0_2_4,d0_3_2,d0_3_3,d0_3_4,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d3_0_3,d3_0_4,d3_1_2,d3_1_3,d3_1_4,d4_3_4]
  ring
#print axioms coefficient_3_4
compact_certificate_declaration theorem coefficient_3_5 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[5]?=some 0 := by
  change some (((((((d0_2_3 y z w b u)*(d1_1_2 y z w b u))+(((d0_2_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_5 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_3_3 y z w b u)*(d1_0_2 y z w b u))+(((d0_3_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_5 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_1_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_4 y z w b u))+((d2_2_2 y z w b u)*(d3_1_3 y z w b u))))+(((d2_3_0 y z w b u)*(d3_0_5 y z w b u))+((d2_3_1 y z w b u)*(d3_0_4 y z w b u)))))+((-1)*(d4_3_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_3,d0_2_4,d0_2_5,d0_3_3,d0_3_4,d0_3_5,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d3_0_4,d3_0_5,d3_1_3,d3_1_4,d3_1_5,d4_3_5]
  ring
#print axioms coefficient_3_5

compact_certificate_declaration theorem coefficient_3_6 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[6]?=some 0 := by
  change some (((((((d0_2_4 y z w b u)*(d1_1_2 y z w b u))+(((d0_2_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_2_6 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_3_4 y z w b u)*(d1_0_2 y z w b u))+(((d0_3_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_6 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_1_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_5 y z w b u))+((d2_2_2 y z w b u)*(d3_1_4 y z w b u))))+(((d2_3_0 y z w b u)*(d3_0_6 y z w b u))+((d2_3_1 y z w b u)*(d3_0_5 y z w b u)))))+((-1)*(d4_3_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_4,d0_2_5,d0_2_6,d0_3_4,d0_3_5,d0_3_6,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d3_0_5,d3_0_6,d3_1_4,d3_1_5,d3_1_6,d4_3_6]
  ring
#print axioms coefficient_3_6
compact_certificate_declaration theorem coefficient_3_7 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[7]?=some 0 := by
  change some (((((((d0_2_5 y z w b u)*(d1_1_2 y z w b u))+((d0_2_6 y z w b u)*(d1_1_1 y z w b u)))+(((d0_3_5 y z w b u)*(d1_0_2 y z w b u))+(((d0_3_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_3_7 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_1_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_1_6 y z w b u))+((d2_2_2 y z w b u)*(d3_1_5 y z w b u))))+((d2_3_1 y z w b u)*(d3_0_6 y z w b u))))+((-1)*(d4_3_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_5,d0_2_6,d0_3_5,d0_3_6,d0_3_7,d1_0_0,d1_0_1,d1_0_2,d1_1_1,d1_1_2,d2_2_0,d2_2_1,d2_2_2,d2_3_1,d3_0_6,d3_1_5,d3_1_6,d3_1_7,d4_3_7]
  ring
#print axioms coefficient_3_7
compact_certificate_declaration theorem coefficient_3_8 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[8]?=some 0 := by
  change some ((((((d0_2_6 y z w b u)*(d1_1_2 y z w b u))+(((d0_3_6 y z w b u)*(d1_0_2 y z w b u))+((d0_3_7 y z w b u)*(d1_0_1 y z w b u))))+(((d2_2_1 y z w b u)*(d3_1_7 y z w b u))+((d2_2_2 y z w b u)*(d3_1_6 y z w b u))))+((-1)*(d4_3_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_6,d0_3_6,d0_3_7,d1_0_1,d1_0_2,d1_1_2,d2_2_1,d2_2_2,d3_1_6,d3_1_7,d4_3_8]
  ring
#print axioms coefficient_3_8

compact_certificate_declaration theorem coefficient_3_9 (y z w b u : ℂ) :
    (innerCertificate3 y z w b u)[9]?=some 0 := by
  change some (((((d0_3_7 y z w b u)*(d1_0_2 y z w b u))+((d2_2_2 y z w b u)*(d3_1_7 y z w b u)))+((-1)*(d4_3_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_7,d1_0_2,d2_2_2,d3_1_7,d4_3_9]
  ring
#print axioms coefficient_3_9

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_4 (y z w b u : ℂ) : (innerCertificate4 y z w b u).length=10 := by
  norm_num [innerCertificate4,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner0_3,inner0_4,inner1_0,inner1_1,inner1_2,inner1_3,inner1_4,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner4_4]
compact_certificate_declaration theorem inner_eval_4 (y z w a b u : ℂ) :
    evaluate a (innerCertificate4 y z w b u)=(((((c0_0 y z w a b u)*(c1_4 y z w a b u))+(((c0_1 y z w a b u)*(c1_3 y z w a b u))+(((c0_2 y z w a b u)*(c1_2 y z w a b u))+(((c0_3 y z w a b u)*(c1_1 y z w a b u))+(((c0_4 y z w a b u)*(c1_0 y z w a b u))+0)))))+(((c2_0 y z w a b u)*(c3_4 y z w a b u))+(((c2_1 y z w a b u)*(c3_3 y z w a b u))+(((c2_2 y z w a b u)*(c3_2 y z w a b u))+(((c2_3 y z w a b u)*(c3_1 y z w a b u))+(((c2_4 y z w a b u)*(c3_0 y z w a b u))+0))))))+((-1)*(c4_4 y z w a b u))) := by
  simp only [innerCertificate4,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_0,c0_1,c0_2,c0_3,c0_4,c1_0,c1_1,c1_2,c1_3,c1_4,c2_0,c2_1,c2_2,c2_3,c2_4,c3_0,c3_1,c3_2,c3_3,c3_4,c4_4]
#print axioms inner_eval_4

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_4_0 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[0]?=some 0 := by
  change some (((((((d0_2_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_3_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_4_0 y z w b u)*(d1_0_0 y z w b u))+0)))+((((d2_2_0 y z w b u)*(d3_2_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_1_0 y z w b u))+0)+(((d2_4_0 y z w b u)*(d3_0_0 y z w b u))+0))))+(((-1)*(d4_4_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_0,d0_3_0,d0_4_0,d1_0_0,d1_1_0,d1_2_0,d2_2_0,d2_3_0,d2_4_0,d3_0_0,d3_1_0,d3_2_0,d4_4_0]
  ring
#print axioms coefficient_4_0
compact_certificate_declaration theorem coefficient_4_1 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[1]?=some 0 := by
  change some (((((((d0_2_0 y z w b u)*(d1_2_1 y z w b u))+(((d0_2_1 y z w b u)*(d1_2_0 y z w b u))+0))+((((d0_3_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_4_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_1 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_2_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_1_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_1_0 y z w b u))+0))+((d2_4_0 y z w b u)*(d3_0_1 y z w b u)))))+((-1)*(d4_4_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_0,d0_2_1,d0_3_0,d0_3_1,d0_4_0,d0_4_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_2_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d3_0_1,d3_1_0,d3_1_1,d3_2_0,d3_2_1,d4_4_1]
  ring
#print axioms coefficient_4_1

compact_certificate_declaration theorem coefficient_4_2 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[2]?=some 0 := by
  change some (((((((d0_2_0 y z w b u)*(d1_2_2 y z w b u))+(((d0_2_1 y z w b u)*(d1_2_1 y z w b u))+(((d0_2_2 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_3_0 y z w b u)*(d1_1_2 y z w b u))+(((d0_3_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_2 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_4_0 y z w b u)*(d1_0_2 y z w b u))+(((d0_4_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_2 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_2_0 y z w b u)*(d3_2_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_2_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_1_2 y z w b u))+((d2_3_1 y z w b u)*(d3_1_1 y z w b u)))+((d2_4_0 y z w b u)*(d3_0_2 y z w b u)))))+((-1)*(d4_4_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_0,d0_2_1,d0_2_2,d0_3_0,d0_3_1,d0_3_2,d0_4_0,d0_4_1,d0_4_2,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_0_2,d3_1_1,d3_1_2,d3_2_0,d3_2_1,d3_2_2,d4_4_2]
  ring
#print axioms coefficient_4_2

compact_certificate_declaration theorem coefficient_4_3 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[3]?=some 0 := by
  change some (((((((d0_2_1 y z w b u)*(d1_2_2 y z w b u))+(((d0_2_2 y z w b u)*(d1_2_1 y z w b u))+(((d0_2_3 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_3_1 y z w b u)*(d1_1_2 y z w b u))+(((d0_3_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_3 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_4_1 y z w b u)*(d1_0_2 y z w b u))+(((d0_4_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_3 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_2_0 y z w b u)*(d3_2_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_2 y z w b u))+((d2_2_2 y z w b u)*(d3_2_1 y z w b u))))+((((d2_3_0 y z w b u)*(d3_1_3 y z w b u))+((d2_3_1 y z w b u)*(d3_1_2 y z w b u)))+((d2_4_0 y z w b u)*(d3_0_3 y z w b u)))))+((-1)*(d4_4_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_1,d0_2_2,d0_2_3,d0_3_1,d0_3_2,d0_3_3,d0_4_1,d0_4_2,d0_4_3,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_0_3,d3_1_2,d3_1_3,d3_2_1,d3_2_2,d3_2_3,d4_4_3]
  ring
#print axioms coefficient_4_3

compact_certificate_declaration theorem coefficient_4_4 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[4]?=some 0 := by
  change some (((((((d0_2_2 y z w b u)*(d1_2_2 y z w b u))+(((d0_2_3 y z w b u)*(d1_2_1 y z w b u))+(((d0_2_4 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_3_2 y z w b u)*(d1_1_2 y z w b u))+(((d0_3_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_4 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_4_2 y z w b u)*(d1_0_2 y z w b u))+(((d0_4_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_4 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_2_0 y z w b u)*(d3_2_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_3 y z w b u))+((d2_2_2 y z w b u)*(d3_2_2 y z w b u))))+((((d2_3_0 y z w b u)*(d3_1_4 y z w b u))+((d2_3_1 y z w b u)*(d3_1_3 y z w b u)))+((d2_4_0 y z w b u)*(d3_0_4 y z w b u)))))+((-1)*(d4_4_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_2,d0_2_3,d0_2_4,d0_3_2,d0_3_3,d0_3_4,d0_4_2,d0_4_3,d0_4_4,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_0_4,d3_1_3,d3_1_4,d3_2_2,d3_2_3,d3_2_4,d4_4_4]
  ring
#print axioms coefficient_4_4
compact_certificate_declaration theorem coefficient_4_5 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[5]?=some 0 := by
  change some (((((((d0_2_3 y z w b u)*(d1_2_2 y z w b u))+(((d0_2_4 y z w b u)*(d1_2_1 y z w b u))+(((d0_2_5 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_3_3 y z w b u)*(d1_1_2 y z w b u))+(((d0_3_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_5 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_4_3 y z w b u)*(d1_0_2 y z w b u))+(((d0_4_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_5 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_2_0 y z w b u)*(d3_2_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_4 y z w b u))+((d2_2_2 y z w b u)*(d3_2_3 y z w b u))))+((((d2_3_0 y z w b u)*(d3_1_5 y z w b u))+((d2_3_1 y z w b u)*(d3_1_4 y z w b u)))+((d2_4_0 y z w b u)*(d3_0_5 y z w b u)))))+((-1)*(d4_4_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_3,d0_2_4,d0_2_5,d0_3_3,d0_3_4,d0_3_5,d0_4_3,d0_4_4,d0_4_5,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_0_5,d3_1_4,d3_1_5,d3_2_3,d3_2_4,d3_2_5,d4_4_5]
  ring
#print axioms coefficient_4_5
compact_certificate_declaration theorem coefficient_4_6 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[6]?=some 0 := by
  change some (((((((d0_2_4 y z w b u)*(d1_2_2 y z w b u))+(((d0_2_5 y z w b u)*(d1_2_1 y z w b u))+(((d0_2_6 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_3_4 y z w b u)*(d1_1_2 y z w b u))+(((d0_3_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_6 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_4_4 y z w b u)*(d1_0_2 y z w b u))+(((d0_4_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_6 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_2_0 y z w b u)*(d3_2_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_5 y z w b u))+((d2_2_2 y z w b u)*(d3_2_4 y z w b u))))+((((d2_3_0 y z w b u)*(d3_1_6 y z w b u))+((d2_3_1 y z w b u)*(d3_1_5 y z w b u)))+((d2_4_0 y z w b u)*(d3_0_6 y z w b u)))))+((-1)*(d4_4_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_4,d0_2_5,d0_2_6,d0_3_4,d0_3_5,d0_3_6,d0_4_4,d0_4_5,d0_4_6,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_0_6,d3_1_5,d3_1_6,d3_2_4,d3_2_5,d3_2_6,d4_4_6]
  ring
#print axioms coefficient_4_6

compact_certificate_declaration theorem coefficient_4_7 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[7]?=some 0 := by
  change some (((((((d0_2_5 y z w b u)*(d1_2_2 y z w b u))+((d0_2_6 y z w b u)*(d1_2_1 y z w b u)))+((((d0_3_5 y z w b u)*(d1_1_2 y z w b u))+(((d0_3_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_3_7 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_4_5 y z w b u)*(d1_0_2 y z w b u))+(((d0_4_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_4_7 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_2_0 y z w b u)*(d3_2_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_2_6 y z w b u))+((d2_2_2 y z w b u)*(d3_2_5 y z w b u))))+(((d2_3_0 y z w b u)*(d3_1_7 y z w b u))+((d2_3_1 y z w b u)*(d3_1_6 y z w b u)))))+((-1)*(d4_4_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_5,d0_2_6,d0_3_5,d0_3_6,d0_3_7,d0_4_5,d0_4_6,d0_4_7,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_1,d1_2_2,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d3_1_6,d3_1_7,d3_2_5,d3_2_6,d3_2_7,d4_4_7]
  ring
#print axioms coefficient_4_7
compact_certificate_declaration theorem coefficient_4_8 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[8]?=some 0 := by
  change some ((((((d0_2_6 y z w b u)*(d1_2_2 y z w b u))+((((d0_3_6 y z w b u)*(d1_1_2 y z w b u))+((d0_3_7 y z w b u)*(d1_1_1 y z w b u)))+(((d0_4_6 y z w b u)*(d1_0_2 y z w b u))+((d0_4_7 y z w b u)*(d1_0_1 y z w b u)))))+((((d2_2_1 y z w b u)*(d3_2_7 y z w b u))+((d2_2_2 y z w b u)*(d3_2_6 y z w b u)))+((d2_3_1 y z w b u)*(d3_1_7 y z w b u))))+((-1)*(d4_4_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_6,d0_3_6,d0_3_7,d0_4_6,d0_4_7,d1_0_1,d1_0_2,d1_1_1,d1_1_2,d1_2_2,d2_2_1,d2_2_2,d2_3_1,d3_1_7,d3_2_6,d3_2_7,d4_4_8]
  ring
#print axioms coefficient_4_8
compact_certificate_declaration theorem coefficient_4_9 (y z w b u : ℂ) :
    (innerCertificate4 y z w b u)[9]?=some 0 := by
  change some ((((((d0_3_7 y z w b u)*(d1_1_2 y z w b u))+((d0_4_7 y z w b u)*(d1_0_2 y z w b u)))+((d2_2_2 y z w b u)*(d3_2_7 y z w b u)))+((-1)*(d4_4_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_7,d0_4_7,d1_0_2,d1_1_2,d2_2_2,d3_2_7,d4_4_9]
  ring
#print axioms coefficient_4_9

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_5 (y z w b u : ℂ) : (innerCertificate5 y z w b u).length=10 := by
  norm_num [innerCertificate5,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner0_3,inner0_4,inner0_5,inner1_0,inner1_1,inner1_2,inner1_3,inner1_4,inner1_5,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner4_5]
compact_certificate_declaration theorem inner_eval_5 (y z w a b u : ℂ) :
    evaluate a (innerCertificate5 y z w b u)=(((((c0_0 y z w a b u)*(c1_5 y z w a b u))+(((c0_1 y z w a b u)*(c1_4 y z w a b u))+(((c0_2 y z w a b u)*(c1_3 y z w a b u))+(((c0_3 y z w a b u)*(c1_2 y z w a b u))+(((c0_4 y z w a b u)*(c1_1 y z w a b u))+(((c0_5 y z w a b u)*(c1_0 y z w a b u))+0))))))+(((c2_0 y z w a b u)*(c3_5 y z w a b u))+(((c2_1 y z w a b u)*(c3_4 y z w a b u))+(((c2_2 y z w a b u)*(c3_3 y z w a b u))+(((c2_3 y z w a b u)*(c3_2 y z w a b u))+((c2_4 y z w a b u)*(c3_1 y z w a b u)))))))+((-1)*(c4_5 y z w a b u))) := by
  simp only [innerCertificate5,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_0,c2_1,c2_2,c2_3,c2_4,c3_1,c3_2,c3_3,c3_4,c3_5,c4_5]
#print axioms inner_eval_5

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_5_0 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[0]?=some 0 := by
  change some (((((((d0_2_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_3_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_4_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_5_0 y z w b u)*(d1_0_0 y z w b u))+0))))+((((d2_2_0 y z w b u)*(d3_3_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_2_0 y z w b u))+0)+(((d2_4_0 y z w b u)*(d3_1_0 y z w b u))+0))))+(((-1)*(d4_5_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_0,d0_3_0,d0_4_0,d0_5_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d2_2_0,d2_3_0,d2_4_0,d3_1_0,d3_2_0,d3_3_0,d4_5_0]
  ring
#print axioms coefficient_5_0

compact_certificate_declaration theorem coefficient_5_1 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[1]?=some 0 := by
  change some (((((((d0_2_0 y z w b u)*(d1_3_1 y z w b u))+(((d0_2_1 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_3_0 y z w b u)*(d1_2_1 y z w b u))+(((d0_3_1 y z w b u)*(d1_2_0 y z w b u))+0))+((((d0_4_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_5_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_1 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_2_0 y z w b u)*(d3_3_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_2_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_2_0 y z w b u))+0))+((d2_4_0 y z w b u)*(d3_1_1 y z w b u)))))+((-1)*(d4_5_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_0,d0_2_1,d0_3_0,d0_3_1,d0_4_0,d0_4_1,d0_5_0,d0_5_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_2_1,d1_3_0,d1_3_1,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d3_1_1,d3_2_0,d3_2_1,d3_3_0,d3_3_1,d4_5_1]
  ring
#print axioms coefficient_5_1

compact_certificate_declaration theorem coefficient_5_2 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[2]?=some 0 := by
  change some (((((((d0_2_1 y z w b u)*(d1_3_1 y z w b u))+(((d0_2_2 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_3_0 y z w b u)*(d1_2_2 y z w b u))+(((d0_3_1 y z w b u)*(d1_2_1 y z w b u))+(((d0_3_2 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_4_0 y z w b u)*(d1_1_2 y z w b u))+(((d0_4_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_2 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_5_0 y z w b u)*(d1_0_2 y z w b u))+(((d0_5_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_2 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_3_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_3_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_2_2 y z w b u))+((d2_3_1 y z w b u)*(d3_2_1 y z w b u)))+((d2_4_0 y z w b u)*(d3_1_2 y z w b u)))))+((-1)*(d4_5_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_1,d0_2_2,d0_3_0,d0_3_1,d0_3_2,d0_4_0,d0_4_1,d0_4_2,d0_5_0,d0_5_1,d0_5_2,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_1_2,d3_2_1,d3_2_2,d3_3_0,d3_3_1,d3_3_2,d4_5_2]
  ring
#print axioms coefficient_5_2

compact_certificate_declaration theorem coefficient_5_3 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[3]?=some 0 := by
  change some (((((((d0_2_2 y z w b u)*(d1_3_1 y z w b u))+(((d0_2_3 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_3_1 y z w b u)*(d1_2_2 y z w b u))+(((d0_3_2 y z w b u)*(d1_2_1 y z w b u))+(((d0_3_3 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_4_1 y z w b u)*(d1_1_2 y z w b u))+(((d0_4_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_3 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_5_1 y z w b u)*(d1_0_2 y z w b u))+(((d0_5_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_3 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_3_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_2 y z w b u))+((d2_2_2 y z w b u)*(d3_3_1 y z w b u))))+((((d2_3_0 y z w b u)*(d3_2_3 y z w b u))+((d2_3_1 y z w b u)*(d3_2_2 y z w b u)))+((d2_4_0 y z w b u)*(d3_1_3 y z w b u)))))+((-1)*(d4_5_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_2,d0_2_3,d0_3_1,d0_3_2,d0_3_3,d0_4_1,d0_4_2,d0_4_3,d0_5_1,d0_5_2,d0_5_3,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_1_3,d3_2_2,d3_2_3,d3_3_1,d3_3_2,d3_3_3,d4_5_3]
  ring
#print axioms coefficient_5_3

compact_certificate_declaration theorem coefficient_5_4 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[4]?=some 0 := by
  change some (((((((d0_2_3 y z w b u)*(d1_3_1 y z w b u))+(((d0_2_4 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_3_2 y z w b u)*(d1_2_2 y z w b u))+(((d0_3_3 y z w b u)*(d1_2_1 y z w b u))+(((d0_3_4 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_4_2 y z w b u)*(d1_1_2 y z w b u))+(((d0_4_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_4 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_5_2 y z w b u)*(d1_0_2 y z w b u))+(((d0_5_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_4 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_3_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_3 y z w b u))+((d2_2_2 y z w b u)*(d3_3_2 y z w b u))))+((((d2_3_0 y z w b u)*(d3_2_4 y z w b u))+((d2_3_1 y z w b u)*(d3_2_3 y z w b u)))+((d2_4_0 y z w b u)*(d3_1_4 y z w b u)))))+((-1)*(d4_5_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_3,d0_2_4,d0_3_2,d0_3_3,d0_3_4,d0_4_2,d0_4_3,d0_4_4,d0_5_2,d0_5_3,d0_5_4,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_1_4,d3_2_3,d3_2_4,d3_3_2,d3_3_3,d3_3_4,d4_5_4]
  ring
#print axioms coefficient_5_4

compact_certificate_declaration theorem coefficient_5_5 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[5]?=some 0 := by
  change some (((((((d0_2_4 y z w b u)*(d1_3_1 y z w b u))+(((d0_2_5 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_3_3 y z w b u)*(d1_2_2 y z w b u))+(((d0_3_4 y z w b u)*(d1_2_1 y z w b u))+(((d0_3_5 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_4_3 y z w b u)*(d1_1_2 y z w b u))+(((d0_4_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_5 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_5_3 y z w b u)*(d1_0_2 y z w b u))+(((d0_5_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_5 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_3_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_4 y z w b u))+((d2_2_2 y z w b u)*(d3_3_3 y z w b u))))+((((d2_3_0 y z w b u)*(d3_2_5 y z w b u))+((d2_3_1 y z w b u)*(d3_2_4 y z w b u)))+((d2_4_0 y z w b u)*(d3_1_5 y z w b u)))))+((-1)*(d4_5_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_4,d0_2_5,d0_3_3,d0_3_4,d0_3_5,d0_4_3,d0_4_4,d0_4_5,d0_5_3,d0_5_4,d0_5_5,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_1_5,d3_2_4,d3_2_5,d3_3_3,d3_3_4,d3_3_5,d4_5_5]
  ring
#print axioms coefficient_5_5
compact_certificate_declaration theorem coefficient_5_6 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[6]?=some 0 := by
  change some (((((((d0_2_5 y z w b u)*(d1_3_1 y z w b u))+(((d0_2_6 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_3_4 y z w b u)*(d1_2_2 y z w b u))+(((d0_3_5 y z w b u)*(d1_2_1 y z w b u))+(((d0_3_6 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_4_4 y z w b u)*(d1_1_2 y z w b u))+(((d0_4_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_6 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_5_4 y z w b u)*(d1_0_2 y z w b u))+(((d0_5_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_6 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_3_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_5 y z w b u))+((d2_2_2 y z w b u)*(d3_3_4 y z w b u))))+((((d2_3_0 y z w b u)*(d3_2_6 y z w b u))+((d2_3_1 y z w b u)*(d3_2_5 y z w b u)))+((d2_4_0 y z w b u)*(d3_1_6 y z w b u)))))+((-1)*(d4_5_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_5,d0_2_6,d0_3_4,d0_3_5,d0_3_6,d0_4_4,d0_4_5,d0_4_6,d0_5_4,d0_5_5,d0_5_6,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_1_6,d3_2_5,d3_2_6,d3_3_4,d3_3_5,d3_3_6,d4_5_6]
  ring
#print axioms coefficient_5_6
compact_certificate_declaration theorem coefficient_5_7 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[7]?=some 0 := by
  change some ((((((d0_2_6 y z w b u)*(d1_3_1 y z w b u))+((((d0_3_5 y z w b u)*(d1_2_2 y z w b u))+(((d0_3_6 y z w b u)*(d1_2_1 y z w b u))+(((d0_3_7 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_4_5 y z w b u)*(d1_1_2 y z w b u))+(((d0_4_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_4_7 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_5_5 y z w b u)*(d1_0_2 y z w b u))+(((d0_5_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_5_7 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_3_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_3_6 y z w b u))+((d2_2_2 y z w b u)*(d3_3_5 y z w b u))))+((((d2_3_0 y z w b u)*(d3_2_7 y z w b u))+((d2_3_1 y z w b u)*(d3_2_6 y z w b u)))+((d2_4_0 y z w b u)*(d3_1_7 y z w b u)))))+((-1)*(d4_5_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_6,d0_3_5,d0_3_6,d0_3_7,d0_4_5,d0_4_6,d0_4_7,d0_5_5,d0_5_6,d0_5_7,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_1,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_1_7,d3_2_6,d3_2_7,d3_3_5,d3_3_6,d3_3_7,d4_5_7]
  ring
#print axioms coefficient_5_7

compact_certificate_declaration theorem coefficient_5_8 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[8]?=some 0 := by
  change some (((((((d0_3_6 y z w b u)*(d1_2_2 y z w b u))+((d0_3_7 y z w b u)*(d1_2_1 y z w b u)))+((((d0_4_6 y z w b u)*(d1_1_2 y z w b u))+((d0_4_7 y z w b u)*(d1_1_1 y z w b u)))+(((d0_5_6 y z w b u)*(d1_0_2 y z w b u))+((d0_5_7 y z w b u)*(d1_0_1 y z w b u)))))+((((d2_2_1 y z w b u)*(d3_3_7 y z w b u))+((d2_2_2 y z w b u)*(d3_3_6 y z w b u)))+((d2_3_1 y z w b u)*(d3_2_7 y z w b u))))+((-1)*(d4_5_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_6,d0_3_7,d0_4_6,d0_4_7,d0_5_6,d0_5_7,d1_0_1,d1_0_2,d1_1_1,d1_1_2,d1_2_1,d1_2_2,d2_2_1,d2_2_2,d2_3_1,d3_2_7,d3_3_6,d3_3_7,d4_5_8]
  ring
#print axioms coefficient_5_8
compact_certificate_declaration theorem coefficient_5_9 (y z w b u : ℂ) :
    (innerCertificate5 y z w b u)[9]?=some 0 := by
  change some ((((((d0_3_7 y z w b u)*(d1_2_2 y z w b u))+(((d0_4_7 y z w b u)*(d1_1_2 y z w b u))+((d0_5_7 y z w b u)*(d1_0_2 y z w b u))))+((d2_2_2 y z w b u)*(d3_3_7 y z w b u)))+((-1)*(d4_5_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_7,d0_4_7,d0_5_7,d1_0_2,d1_1_2,d1_2_2,d2_2_2,d3_3_7,d4_5_9]
  ring
#print axioms coefficient_5_9

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_6 (y z w b u : ℂ) : (innerCertificate6 y z w b u).length=10 := by
  norm_num [innerCertificate6,add,multiply,scale,inner0_1,inner0_2,inner0_3,inner0_4,inner0_5,inner0_6,inner1_0,inner1_1,inner1_2,inner1_3,inner1_4,inner1_5,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner4_6]
compact_certificate_declaration theorem inner_eval_6 (y z w a b u : ℂ) :
    evaluate a (innerCertificate6 y z w b u)=(((((c0_1 y z w a b u)*(c1_5 y z w a b u))+(((c0_2 y z w a b u)*(c1_4 y z w a b u))+(((c0_3 y z w a b u)*(c1_3 y z w a b u))+(((c0_4 y z w a b u)*(c1_2 y z w a b u))+(((c0_5 y z w a b u)*(c1_1 y z w a b u))+(((c0_6 y z w a b u)*(c1_0 y z w a b u))+0))))))+(((c2_0 y z w a b u)*(c3_6 y z w a b u))+(((c2_1 y z w a b u)*(c3_5 y z w a b u))+(((c2_2 y z w a b u)*(c3_4 y z w a b u))+(((c2_3 y z w a b u)*(c3_3 y z w a b u))+((c2_4 y z w a b u)*(c3_2 y z w a b u)))))))+((-1)*(c4_6 y z w a b u))) := by
  simp only [innerCertificate6,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_0,c2_1,c2_2,c2_3,c2_4,c3_2,c3_3,c3_4,c3_5,c3_6,c4_6]
#print axioms inner_eval_6

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_6_0 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[0]?=some 0 := by
  change some (((((((d0_2_0 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_3_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_4_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_5_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_6_0 y z w b u)*(d1_0_0 y z w b u))+0)))))+((((d2_2_0 y z w b u)*(d3_4_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_3_0 y z w b u))+0)+(((d2_4_0 y z w b u)*(d3_2_0 y z w b u))+0))))+(((-1)*(d4_6_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_0,d0_3_0,d0_4_0,d0_5_0,d0_6_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d1_4_0,d2_2_0,d2_3_0,d2_4_0,d3_2_0,d3_3_0,d3_4_0,d4_6_0]
  ring
#print axioms coefficient_6_0

compact_certificate_declaration theorem coefficient_6_1 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[1]?=some 0 := by
  change some (((((((d0_2_1 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_3_0 y z w b u)*(d1_3_1 y z w b u))+(((d0_3_1 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_4_0 y z w b u)*(d1_2_1 y z w b u))+(((d0_4_1 y z w b u)*(d1_2_0 y z w b u))+0))+((((d0_5_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_6_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_1 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_4_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_3_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_3_0 y z w b u))+0))+((d2_4_0 y z w b u)*(d3_2_1 y z w b u)))))+((-1)*(d4_6_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_1,d0_3_0,d0_3_1,d0_4_0,d0_4_1,d0_5_0,d0_5_1,d0_6_0,d0_6_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_2_1,d1_3_0,d1_3_1,d1_4_0,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d3_2_1,d3_3_0,d3_3_1,d3_4_0,d3_4_1,d4_6_1]
  ring
#print axioms coefficient_6_1

compact_certificate_declaration theorem coefficient_6_2 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[2]?=some 0 := by
  change some (((((((d0_2_2 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_3_1 y z w b u)*(d1_3_1 y z w b u))+(((d0_3_2 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_4_0 y z w b u)*(d1_2_2 y z w b u))+(((d0_4_1 y z w b u)*(d1_2_1 y z w b u))+(((d0_4_2 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_5_0 y z w b u)*(d1_1_2 y z w b u))+(((d0_5_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_2 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_6_0 y z w b u)*(d1_0_2 y z w b u))+(((d0_6_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_2 y z w b u)*(d1_0_0 y z w b u))+0)))))))+((((d2_2_0 y z w b u)*(d3_4_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_4_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_3_2 y z w b u))+((d2_3_1 y z w b u)*(d3_3_1 y z w b u)))+((d2_4_0 y z w b u)*(d3_2_2 y z w b u)))))+((-1)*(d4_6_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_2,d0_3_1,d0_3_2,d0_4_0,d0_4_1,d0_4_2,d0_5_0,d0_5_1,d0_5_2,d0_6_0,d0_6_1,d0_6_2,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_2_2,d3_3_1,d3_3_2,d3_4_0,d3_4_1,d3_4_2,d4_6_2]
  ring
#print axioms coefficient_6_2

compact_certificate_declaration theorem coefficient_6_3 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[3]?=some 0 := by
  change some (((((((d0_2_3 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_3_2 y z w b u)*(d1_3_1 y z w b u))+(((d0_3_3 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_4_1 y z w b u)*(d1_2_2 y z w b u))+(((d0_4_2 y z w b u)*(d1_2_1 y z w b u))+(((d0_4_3 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_5_1 y z w b u)*(d1_1_2 y z w b u))+(((d0_5_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_3 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_6_1 y z w b u)*(d1_0_2 y z w b u))+(((d0_6_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_3 y z w b u)*(d1_0_0 y z w b u))+0)))))))+((((d2_2_0 y z w b u)*(d3_4_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_2 y z w b u))+((d2_2_2 y z w b u)*(d3_4_1 y z w b u))))+((((d2_3_0 y z w b u)*(d3_3_3 y z w b u))+((d2_3_1 y z w b u)*(d3_3_2 y z w b u)))+((d2_4_0 y z w b u)*(d3_2_3 y z w b u)))))+((-1)*(d4_6_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_3,d0_3_2,d0_3_3,d0_4_1,d0_4_2,d0_4_3,d0_5_1,d0_5_2,d0_5_3,d0_6_1,d0_6_2,d0_6_3,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_2_3,d3_3_2,d3_3_3,d3_4_1,d3_4_2,d3_4_3,d4_6_3]
  ring
#print axioms coefficient_6_3

compact_certificate_declaration theorem coefficient_6_4 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[4]?=some 0 := by
  change some (((((((d0_2_4 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_3_3 y z w b u)*(d1_3_1 y z w b u))+(((d0_3_4 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_4_2 y z w b u)*(d1_2_2 y z w b u))+(((d0_4_3 y z w b u)*(d1_2_1 y z w b u))+(((d0_4_4 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_5_2 y z w b u)*(d1_1_2 y z w b u))+(((d0_5_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_4 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_6_2 y z w b u)*(d1_0_2 y z w b u))+(((d0_6_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_4 y z w b u)*(d1_0_0 y z w b u))+0)))))))+((((d2_2_0 y z w b u)*(d3_4_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_3 y z w b u))+((d2_2_2 y z w b u)*(d3_4_2 y z w b u))))+((((d2_3_0 y z w b u)*(d3_3_4 y z w b u))+((d2_3_1 y z w b u)*(d3_3_3 y z w b u)))+((d2_4_0 y z w b u)*(d3_2_4 y z w b u)))))+((-1)*(d4_6_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_4,d0_3_3,d0_3_4,d0_4_2,d0_4_3,d0_4_4,d0_5_2,d0_5_3,d0_5_4,d0_6_2,d0_6_3,d0_6_4,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_2_4,d3_3_3,d3_3_4,d3_4_2,d3_4_3,d3_4_4,d4_6_4]
  ring
#print axioms coefficient_6_4

compact_certificate_declaration theorem coefficient_6_5 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[5]?=some 0 := by
  change some (((((((d0_2_5 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_3_4 y z w b u)*(d1_3_1 y z w b u))+(((d0_3_5 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_4_3 y z w b u)*(d1_2_2 y z w b u))+(((d0_4_4 y z w b u)*(d1_2_1 y z w b u))+(((d0_4_5 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_5_3 y z w b u)*(d1_1_2 y z w b u))+(((d0_5_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_5 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_6_3 y z w b u)*(d1_0_2 y z w b u))+(((d0_6_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_5 y z w b u)*(d1_0_0 y z w b u))+0)))))))+((((d2_2_0 y z w b u)*(d3_4_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_4 y z w b u))+((d2_2_2 y z w b u)*(d3_4_3 y z w b u))))+((((d2_3_0 y z w b u)*(d3_3_5 y z w b u))+((d2_3_1 y z w b u)*(d3_3_4 y z w b u)))+((d2_4_0 y z w b u)*(d3_2_5 y z w b u)))))+((-1)*(d4_6_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_5,d0_3_4,d0_3_5,d0_4_3,d0_4_4,d0_4_5,d0_5_3,d0_5_4,d0_5_5,d0_6_3,d0_6_4,d0_6_5,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_2_5,d3_3_4,d3_3_5,d3_4_3,d3_4_4,d3_4_5,d4_6_5]
  ring
#print axioms coefficient_6_5
compact_certificate_declaration theorem coefficient_6_6 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[6]?=some 0 := by
  change some (((((((d0_2_6 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_3_5 y z w b u)*(d1_3_1 y z w b u))+(((d0_3_6 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_4_4 y z w b u)*(d1_2_2 y z w b u))+(((d0_4_5 y z w b u)*(d1_2_1 y z w b u))+(((d0_4_6 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_5_4 y z w b u)*(d1_1_2 y z w b u))+(((d0_5_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_6 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_6_4 y z w b u)*(d1_0_2 y z w b u))+(((d0_6_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_6 y z w b u)*(d1_0_0 y z w b u))+0)))))))+((((d2_2_0 y z w b u)*(d3_4_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_5 y z w b u))+((d2_2_2 y z w b u)*(d3_4_4 y z w b u))))+((((d2_3_0 y z w b u)*(d3_3_6 y z w b u))+((d2_3_1 y z w b u)*(d3_3_5 y z w b u)))+((d2_4_0 y z w b u)*(d3_2_6 y z w b u)))))+((-1)*(d4_6_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_6,d0_3_5,d0_3_6,d0_4_4,d0_4_5,d0_4_6,d0_5_4,d0_5_5,d0_5_6,d0_6_4,d0_6_5,d0_6_6,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_2_6,d3_3_5,d3_3_6,d3_4_4,d3_4_5,d3_4_6,d4_6_6]
  ring
#print axioms coefficient_6_6
compact_certificate_declaration theorem coefficient_6_7 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[7]?=some 0 := by
  change some (((((((d0_3_6 y z w b u)*(d1_3_1 y z w b u))+(((d0_3_7 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_4_5 y z w b u)*(d1_2_2 y z w b u))+(((d0_4_6 y z w b u)*(d1_2_1 y z w b u))+(((d0_4_7 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_5_5 y z w b u)*(d1_1_2 y z w b u))+(((d0_5_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_5_7 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_6_5 y z w b u)*(d1_0_2 y z w b u))+(((d0_6_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_6_7 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_4_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_4_6 y z w b u))+((d2_2_2 y z w b u)*(d3_4_5 y z w b u))))+((((d2_3_0 y z w b u)*(d3_3_7 y z w b u))+((d2_3_1 y z w b u)*(d3_3_6 y z w b u)))+((d2_4_0 y z w b u)*(d3_2_7 y z w b u)))))+((-1)*(d4_6_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_6,d0_3_7,d0_4_5,d0_4_6,d0_4_7,d0_5_5,d0_5_6,d0_5_7,d0_6_5,d0_6_6,d0_6_7,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_2_7,d3_3_6,d3_3_7,d3_4_5,d3_4_6,d3_4_7,d4_6_7]
  ring
#print axioms coefficient_6_7

compact_certificate_declaration theorem coefficient_6_8 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[8]?=some 0 := by
  change some ((((((d0_3_7 y z w b u)*(d1_3_1 y z w b u))+((((d0_4_6 y z w b u)*(d1_2_2 y z w b u))+((d0_4_7 y z w b u)*(d1_2_1 y z w b u)))+((((d0_5_6 y z w b u)*(d1_1_2 y z w b u))+((d0_5_7 y z w b u)*(d1_1_1 y z w b u)))+(((d0_6_6 y z w b u)*(d1_0_2 y z w b u))+((d0_6_7 y z w b u)*(d1_0_1 y z w b u))))))+((((d2_2_1 y z w b u)*(d3_4_7 y z w b u))+((d2_2_2 y z w b u)*(d3_4_6 y z w b u)))+((d2_3_1 y z w b u)*(d3_3_7 y z w b u))))+((-1)*(d4_6_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_7,d0_4_6,d0_4_7,d0_5_6,d0_5_7,d0_6_6,d0_6_7,d1_0_1,d1_0_2,d1_1_1,d1_1_2,d1_2_1,d1_2_2,d1_3_1,d2_2_1,d2_2_2,d2_3_1,d3_3_7,d3_4_6,d3_4_7,d4_6_8]
  ring
#print axioms coefficient_6_8
compact_certificate_declaration theorem coefficient_6_9 (y z w b u : ℂ) :
    (innerCertificate6 y z w b u)[9]?=some 0 := by
  change some ((((((d0_4_7 y z w b u)*(d1_2_2 y z w b u))+(((d0_5_7 y z w b u)*(d1_1_2 y z w b u))+((d0_6_7 y z w b u)*(d1_0_2 y z w b u))))+((d2_2_2 y z w b u)*(d3_4_7 y z w b u)))+((-1)*(d4_6_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_7,d0_5_7,d0_6_7,d1_0_2,d1_1_2,d1_2_2,d2_2_2,d3_4_7,d4_6_9]
  ring
#print axioms coefficient_6_9

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_7 (y z w b u : ℂ) : (innerCertificate7 y z w b u).length=10 := by
  norm_num [innerCertificate7,add,multiply,scale,inner0_2,inner0_3,inner0_4,inner0_5,inner0_6,inner0_7,inner1_0,inner1_1,inner1_2,inner1_3,inner1_4,inner1_5,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner4_7]
compact_certificate_declaration theorem inner_eval_7 (y z w a b u : ℂ) :
    evaluate a (innerCertificate7 y z w b u)=(((((c0_2 y z w a b u)*(c1_5 y z w a b u))+(((c0_3 y z w a b u)*(c1_4 y z w a b u))+(((c0_4 y z w a b u)*(c1_3 y z w a b u))+(((c0_5 y z w a b u)*(c1_2 y z w a b u))+(((c0_6 y z w a b u)*(c1_1 y z w a b u))+(((c0_7 y z w a b u)*(c1_0 y z w a b u))+0))))))+(((c2_0 y z w a b u)*(c3_7 y z w a b u))+(((c2_1 y z w a b u)*(c3_6 y z w a b u))+(((c2_2 y z w a b u)*(c3_5 y z w a b u))+(((c2_3 y z w a b u)*(c3_4 y z w a b u))+((c2_4 y z w a b u)*(c3_3 y z w a b u)))))))+((-1)*(c4_7 y z w a b u))) := by
  simp only [innerCertificate7,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_0,c2_1,c2_2,c2_3,c2_4,c3_3,c3_4,c3_5,c3_6,c3_7,c4_7]
#print axioms inner_eval_7

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_7_0 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[0]?=some 0 := by
  change some (((((((d0_2_0 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_3_0 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_4_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_5_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_6_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_7_0 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_5_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_4_0 y z w b u))+0)+(((d2_4_0 y z w b u)*(d3_3_0 y z w b u))+0))))+(((-1)*(d4_7_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_0,d0_3_0,d0_4_0,d0_5_0,d0_6_0,d0_7_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d1_4_0,d1_5_0,d2_2_0,d2_3_0,d2_4_0,d3_3_0,d3_4_0,d3_5_0,d4_7_0]
  ring
#print axioms coefficient_7_0

compact_certificate_declaration theorem coefficient_7_1 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[1]?=some 0 := by
  change some (((((((d0_2_1 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_3_1 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_4_0 y z w b u)*(d1_3_1 y z w b u))+(((d0_4_1 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_5_0 y z w b u)*(d1_2_1 y z w b u))+(((d0_5_1 y z w b u)*(d1_2_0 y z w b u))+0))+((((d0_6_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_7_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_1 y z w b u)*(d1_0_0 y z w b u))+0)))))))+((((d2_2_0 y z w b u)*(d3_5_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_4_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_4_0 y z w b u))+0))+((d2_4_0 y z w b u)*(d3_3_1 y z w b u)))))+((-1)*(d4_7_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_1,d0_3_1,d0_4_0,d0_4_1,d0_5_0,d0_5_1,d0_6_0,d0_6_1,d0_7_0,d0_7_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_2_1,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d3_3_1,d3_4_0,d3_4_1,d3_5_0,d3_5_1,d4_7_1]
  ring
#print axioms coefficient_7_1

compact_certificate_declaration theorem coefficient_7_2 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[2]?=some 0 := by
  change some (((((((d0_2_2 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_3_2 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_4_1 y z w b u)*(d1_3_1 y z w b u))+(((d0_4_2 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_5_0 y z w b u)*(d1_2_2 y z w b u))+(((d0_5_1 y z w b u)*(d1_2_1 y z w b u))+(((d0_5_2 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_6_0 y z w b u)*(d1_1_2 y z w b u))+(((d0_6_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_2 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_7_0 y z w b u)*(d1_0_2 y z w b u))+(((d0_7_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_2 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_5_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_5_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_4_2 y z w b u))+((d2_3_1 y z w b u)*(d3_4_1 y z w b u)))+((d2_4_0 y z w b u)*(d3_3_2 y z w b u)))))+((-1)*(d4_7_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_2,d0_3_2,d0_4_1,d0_4_2,d0_5_0,d0_5_1,d0_5_2,d0_6_0,d0_6_1,d0_6_2,d0_7_0,d0_7_1,d0_7_2,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_3_2,d3_4_1,d3_4_2,d3_5_0,d3_5_1,d3_5_2,d4_7_2]
  ring
#print axioms coefficient_7_2

compact_certificate_declaration theorem coefficient_7_3 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[3]?=some 0 := by
  change some (((((((d0_2_3 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_3_3 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_4_2 y z w b u)*(d1_3_1 y z w b u))+(((d0_4_3 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_5_1 y z w b u)*(d1_2_2 y z w b u))+(((d0_5_2 y z w b u)*(d1_2_1 y z w b u))+(((d0_5_3 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_6_1 y z w b u)*(d1_1_2 y z w b u))+(((d0_6_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_3 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_7_1 y z w b u)*(d1_0_2 y z w b u))+(((d0_7_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_3 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_5_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_2 y z w b u))+((d2_2_2 y z w b u)*(d3_5_1 y z w b u))))+((((d2_3_0 y z w b u)*(d3_4_3 y z w b u))+((d2_3_1 y z w b u)*(d3_4_2 y z w b u)))+((d2_4_0 y z w b u)*(d3_3_3 y z w b u)))))+((-1)*(d4_7_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_3,d0_3_3,d0_4_2,d0_4_3,d0_5_1,d0_5_2,d0_5_3,d0_6_1,d0_6_2,d0_6_3,d0_7_1,d0_7_2,d0_7_3,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_3_3,d3_4_2,d3_4_3,d3_5_1,d3_5_2,d3_5_3,d4_7_3]
  ring
#print axioms coefficient_7_3

compact_certificate_declaration theorem coefficient_7_4 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[4]?=some 0 := by
  change some (((((((d0_2_4 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_3_4 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_4_3 y z w b u)*(d1_3_1 y z w b u))+(((d0_4_4 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_5_2 y z w b u)*(d1_2_2 y z w b u))+(((d0_5_3 y z w b u)*(d1_2_1 y z w b u))+(((d0_5_4 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_6_2 y z w b u)*(d1_1_2 y z w b u))+(((d0_6_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_4 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_7_2 y z w b u)*(d1_0_2 y z w b u))+(((d0_7_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_4 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_5_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_3 y z w b u))+((d2_2_2 y z w b u)*(d3_5_2 y z w b u))))+((((d2_3_0 y z w b u)*(d3_4_4 y z w b u))+((d2_3_1 y z w b u)*(d3_4_3 y z w b u)))+((d2_4_0 y z w b u)*(d3_3_4 y z w b u)))))+((-1)*(d4_7_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_4,d0_3_4,d0_4_3,d0_4_4,d0_5_2,d0_5_3,d0_5_4,d0_6_2,d0_6_3,d0_6_4,d0_7_2,d0_7_3,d0_7_4,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_3_4,d3_4_3,d3_4_4,d3_5_2,d3_5_3,d3_5_4,d4_7_4]
  ring
#print axioms coefficient_7_4

compact_certificate_declaration theorem coefficient_7_5 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[5]?=some 0 := by
  change some (((((((d0_2_5 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_3_5 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_4_4 y z w b u)*(d1_3_1 y z w b u))+(((d0_4_5 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_5_3 y z w b u)*(d1_2_2 y z w b u))+(((d0_5_4 y z w b u)*(d1_2_1 y z w b u))+(((d0_5_5 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_6_3 y z w b u)*(d1_1_2 y z w b u))+(((d0_6_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_5 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_7_3 y z w b u)*(d1_0_2 y z w b u))+(((d0_7_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_5 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_5_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_4 y z w b u))+((d2_2_2 y z w b u)*(d3_5_3 y z w b u))))+((((d2_3_0 y z w b u)*(d3_4_5 y z w b u))+((d2_3_1 y z w b u)*(d3_4_4 y z w b u)))+((d2_4_0 y z w b u)*(d3_3_5 y z w b u)))))+((-1)*(d4_7_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_5,d0_3_5,d0_4_4,d0_4_5,d0_5_3,d0_5_4,d0_5_5,d0_6_3,d0_6_4,d0_6_5,d0_7_3,d0_7_4,d0_7_5,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_3_5,d3_4_4,d3_4_5,d3_5_3,d3_5_4,d3_5_5,d4_7_5]
  ring
#print axioms coefficient_7_5
compact_certificate_declaration theorem coefficient_7_6 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[6]?=some 0 := by
  change some (((((((d0_2_6 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_3_6 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_4_5 y z w b u)*(d1_3_1 y z w b u))+(((d0_4_6 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_5_4 y z w b u)*(d1_2_2 y z w b u))+(((d0_5_5 y z w b u)*(d1_2_1 y z w b u))+(((d0_5_6 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_6_4 y z w b u)*(d1_1_2 y z w b u))+(((d0_6_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_6 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_7_4 y z w b u)*(d1_0_2 y z w b u))+(((d0_7_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_6 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_5_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_5 y z w b u))+((d2_2_2 y z w b u)*(d3_5_4 y z w b u))))+((((d2_3_0 y z w b u)*(d3_4_6 y z w b u))+((d2_3_1 y z w b u)*(d3_4_5 y z w b u)))+((d2_4_0 y z w b u)*(d3_3_6 y z w b u)))))+((-1)*(d4_7_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_6,d0_3_6,d0_4_5,d0_4_6,d0_5_4,d0_5_5,d0_5_6,d0_6_4,d0_6_5,d0_6_6,d0_7_4,d0_7_5,d0_7_6,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_3_6,d3_4_5,d3_4_6,d3_5_4,d3_5_5,d3_5_6,d4_7_6]
  ring
#print axioms coefficient_7_6
compact_certificate_declaration theorem coefficient_7_7 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[7]?=some 0 := by
  change some (((((((d0_3_7 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_4_6 y z w b u)*(d1_3_1 y z w b u))+(((d0_4_7 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_5_5 y z w b u)*(d1_2_2 y z w b u))+(((d0_5_6 y z w b u)*(d1_2_1 y z w b u))+(((d0_5_7 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_6_5 y z w b u)*(d1_1_2 y z w b u))+(((d0_6_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_6_7 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_7_5 y z w b u)*(d1_0_2 y z w b u))+(((d0_7_6 y z w b u)*(d1_0_1 y z w b u))+(((d0_7_7 y z w b u)*(d1_0_0 y z w b u))+0)))))))+((((d2_2_0 y z w b u)*(d3_5_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_5_6 y z w b u))+((d2_2_2 y z w b u)*(d3_5_5 y z w b u))))+((((d2_3_0 y z w b u)*(d3_4_7 y z w b u))+((d2_3_1 y z w b u)*(d3_4_6 y z w b u)))+((d2_4_0 y z w b u)*(d3_3_7 y z w b u)))))+((-1)*(d4_7_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_7,d0_4_6,d0_4_7,d0_5_5,d0_5_6,d0_5_7,d0_6_5,d0_6_6,d0_6_7,d0_7_5,d0_7_6,d0_7_7,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_3_7,d3_4_6,d3_4_7,d3_5_5,d3_5_6,d3_5_7,d4_7_7]
  ring
#print axioms coefficient_7_7

compact_certificate_declaration theorem coefficient_7_8 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[8]?=some 0 := by
  change some ((((((d0_4_7 y z w b u)*(d1_3_1 y z w b u))+((((d0_5_6 y z w b u)*(d1_2_2 y z w b u))+((d0_5_7 y z w b u)*(d1_2_1 y z w b u)))+((((d0_6_6 y z w b u)*(d1_1_2 y z w b u))+((d0_6_7 y z w b u)*(d1_1_1 y z w b u)))+(((d0_7_6 y z w b u)*(d1_0_2 y z w b u))+((d0_7_7 y z w b u)*(d1_0_1 y z w b u))))))+((((d2_2_1 y z w b u)*(d3_5_7 y z w b u))+((d2_2_2 y z w b u)*(d3_5_6 y z w b u)))+((d2_3_1 y z w b u)*(d3_4_7 y z w b u))))+((-1)*(d4_7_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_7,d0_5_6,d0_5_7,d0_6_6,d0_6_7,d0_7_6,d0_7_7,d1_0_1,d1_0_2,d1_1_1,d1_1_2,d1_2_1,d1_2_2,d1_3_1,d2_2_1,d2_2_2,d2_3_1,d3_4_7,d3_5_6,d3_5_7,d4_7_8]
  ring
#print axioms coefficient_7_8
compact_certificate_declaration theorem coefficient_7_9 (y z w b u : ℂ) :
    (innerCertificate7 y z w b u)[9]?=some 0 := by
  change some ((((((d0_5_7 y z w b u)*(d1_2_2 y z w b u))+(((d0_6_7 y z w b u)*(d1_1_2 y z w b u))+((d0_7_7 y z w b u)*(d1_0_2 y z w b u))))+((d2_2_2 y z w b u)*(d3_5_7 y z w b u)))+((-1)*(d4_7_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_5_7,d0_6_7,d0_7_7,d1_0_2,d1_1_2,d1_2_2,d2_2_2,d3_5_7,d4_7_9]
  ring
#print axioms coefficient_7_9

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_8 (y z w b u : ℂ) : (innerCertificate8 y z w b u).length=10 := by
  norm_num [innerCertificate8,add,multiply,scale,inner0_3,inner0_4,inner0_5,inner0_6,inner0_7,inner0_8,inner1_0,inner1_1,inner1_2,inner1_3,inner1_4,inner1_5,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner4_8]
compact_certificate_declaration theorem inner_eval_8 (y z w a b u : ℂ) :
    evaluate a (innerCertificate8 y z w b u)=(((((c0_3 y z w a b u)*(c1_5 y z w a b u))+(((c0_4 y z w a b u)*(c1_4 y z w a b u))+(((c0_5 y z w a b u)*(c1_3 y z w a b u))+(((c0_6 y z w a b u)*(c1_2 y z w a b u))+(((c0_7 y z w a b u)*(c1_1 y z w a b u))+(((c0_8 y z w a b u)*(c1_0 y z w a b u))+0))))))+(((c2_0 y z w a b u)*(c3_8 y z w a b u))+(((c2_1 y z w a b u)*(c3_7 y z w a b u))+(((c2_2 y z w a b u)*(c3_6 y z w a b u))+(((c2_3 y z w a b u)*(c3_5 y z w a b u))+((c2_4 y z w a b u)*(c3_4 y z w a b u)))))))+((-1)*(c4_8 y z w a b u))) := by
  simp only [innerCertificate8,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_0,c2_1,c2_2,c2_3,c2_4,c3_4,c3_5,c3_6,c3_7,c3_8,c4_8]
#print axioms inner_eval_8

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_8_0 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[0]?=some 0 := by
  change some (((((((d0_3_0 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_4_0 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_5_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_6_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_7_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_8_0 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_6_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_5_0 y z w b u))+0)+(((d2_4_0 y z w b u)*(d3_4_0 y z w b u))+0))))+(((-1)*(d4_8_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_0,d0_4_0,d0_5_0,d0_6_0,d0_7_0,d0_8_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d1_4_0,d1_5_0,d2_2_0,d2_3_0,d2_4_0,d3_4_0,d3_5_0,d3_6_0,d4_8_0]
  ring
#print axioms coefficient_8_0

compact_certificate_declaration theorem coefficient_8_1 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[1]?=some 0 := by
  change some (((((((d0_3_1 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_4_1 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_5_0 y z w b u)*(d1_3_1 y z w b u))+(((d0_5_1 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_6_0 y z w b u)*(d1_2_1 y z w b u))+(((d0_6_1 y z w b u)*(d1_2_0 y z w b u))+0))+((((d0_7_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_7_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_8_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_8_1 y z w b u)*(d1_0_0 y z w b u))+0)))))))+((((d2_2_0 y z w b u)*(d3_6_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_6_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_5_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_5_0 y z w b u))+0))+((d2_4_0 y z w b u)*(d3_4_1 y z w b u)))))+((-1)*(d4_8_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_1,d0_4_1,d0_5_0,d0_5_1,d0_6_0,d0_6_1,d0_7_0,d0_7_1,d0_8_0,d0_8_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_2_1,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d3_4_1,d3_5_0,d3_5_1,d3_6_0,d3_6_1,d4_8_1]
  ring
#print axioms coefficient_8_1

compact_certificate_declaration theorem coefficient_8_2 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[2]?=some 0 := by
  change some (((((((d0_3_2 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_4_2 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_5_1 y z w b u)*(d1_3_1 y z w b u))+(((d0_5_2 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_6_0 y z w b u)*(d1_2_2 y z w b u))+(((d0_6_1 y z w b u)*(d1_2_1 y z w b u))+(((d0_6_2 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_7_0 y z w b u)*(d1_1_2 y z w b u))+(((d0_7_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_7_2 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_8_0 y z w b u)*(d1_0_2 y z w b u))+(((d0_8_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_8_2 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_6_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_6_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_6_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_5_2 y z w b u))+((d2_3_1 y z w b u)*(d3_5_1 y z w b u)))+((d2_4_0 y z w b u)*(d3_4_2 y z w b u)))))+((-1)*(d4_8_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_2,d0_4_2,d0_5_1,d0_5_2,d0_6_0,d0_6_1,d0_6_2,d0_7_0,d0_7_1,d0_7_2,d0_8_0,d0_8_1,d0_8_2,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_4_2,d3_5_1,d3_5_2,d3_6_0,d3_6_1,d3_6_2,d4_8_2]
  ring
#print axioms coefficient_8_2

compact_certificate_declaration theorem coefficient_8_3 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[3]?=some 0 := by
  change some (((((((d0_3_3 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_4_3 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_5_2 y z w b u)*(d1_3_1 y z w b u))+(((d0_5_3 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_6_1 y z w b u)*(d1_2_2 y z w b u))+(((d0_6_2 y z w b u)*(d1_2_1 y z w b u))+(((d0_6_3 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_7_1 y z w b u)*(d1_1_2 y z w b u))+(((d0_7_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_7_3 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_8_1 y z w b u)*(d1_0_2 y z w b u))+(((d0_8_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_8_3 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_6_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_6_2 y z w b u))+((d2_2_2 y z w b u)*(d3_6_1 y z w b u))))+((((d2_3_0 y z w b u)*(d3_5_3 y z w b u))+((d2_3_1 y z w b u)*(d3_5_2 y z w b u)))+((d2_4_0 y z w b u)*(d3_4_3 y z w b u)))))+((-1)*(d4_8_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_3,d0_4_3,d0_5_2,d0_5_3,d0_6_1,d0_6_2,d0_6_3,d0_7_1,d0_7_2,d0_7_3,d0_8_1,d0_8_2,d0_8_3,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_4_3,d3_5_2,d3_5_3,d3_6_1,d3_6_2,d3_6_3,d4_8_3]
  ring
#print axioms coefficient_8_3

compact_certificate_declaration theorem coefficient_8_4 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[4]?=some 0 := by
  change some (((((((d0_3_4 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_4_4 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_5_3 y z w b u)*(d1_3_1 y z w b u))+(((d0_5_4 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_6_2 y z w b u)*(d1_2_2 y z w b u))+(((d0_6_3 y z w b u)*(d1_2_1 y z w b u))+(((d0_6_4 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_7_2 y z w b u)*(d1_1_2 y z w b u))+(((d0_7_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_7_4 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_8_2 y z w b u)*(d1_0_2 y z w b u))+(((d0_8_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_8_4 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_6_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_6_3 y z w b u))+((d2_2_2 y z w b u)*(d3_6_2 y z w b u))))+((((d2_3_0 y z w b u)*(d3_5_4 y z w b u))+((d2_3_1 y z w b u)*(d3_5_3 y z w b u)))+((d2_4_0 y z w b u)*(d3_4_4 y z w b u)))))+((-1)*(d4_8_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_4,d0_4_4,d0_5_3,d0_5_4,d0_6_2,d0_6_3,d0_6_4,d0_7_2,d0_7_3,d0_7_4,d0_8_2,d0_8_3,d0_8_4,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_4_4,d3_5_3,d3_5_4,d3_6_2,d3_6_3,d3_6_4,d4_8_4]
  ring
#print axioms coefficient_8_4

compact_certificate_declaration theorem coefficient_8_5 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[5]?=some 0 := by
  change some (((((((d0_3_5 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_4_5 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_5_4 y z w b u)*(d1_3_1 y z w b u))+(((d0_5_5 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_6_3 y z w b u)*(d1_2_2 y z w b u))+(((d0_6_4 y z w b u)*(d1_2_1 y z w b u))+(((d0_6_5 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_7_3 y z w b u)*(d1_1_2 y z w b u))+(((d0_7_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_7_5 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_8_3 y z w b u)*(d1_0_2 y z w b u))+(((d0_8_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_8_5 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_6_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_6_4 y z w b u))+((d2_2_2 y z w b u)*(d3_6_3 y z w b u))))+((((d2_3_0 y z w b u)*(d3_5_5 y z w b u))+((d2_3_1 y z w b u)*(d3_5_4 y z w b u)))+((d2_4_0 y z w b u)*(d3_4_5 y z w b u)))))+((-1)*(d4_8_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_5,d0_4_5,d0_5_4,d0_5_5,d0_6_3,d0_6_4,d0_6_5,d0_7_3,d0_7_4,d0_7_5,d0_8_3,d0_8_4,d0_8_5,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_4_5,d3_5_4,d3_5_5,d3_6_3,d3_6_4,d3_6_5,d4_8_5]
  ring
#print axioms coefficient_8_5
compact_certificate_declaration theorem coefficient_8_6 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[6]?=some 0 := by
  change some (((((((d0_3_6 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_4_6 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_5_5 y z w b u)*(d1_3_1 y z w b u))+(((d0_5_6 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_6_4 y z w b u)*(d1_2_2 y z w b u))+(((d0_6_5 y z w b u)*(d1_2_1 y z w b u))+(((d0_6_6 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_7_4 y z w b u)*(d1_1_2 y z w b u))+(((d0_7_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_7_6 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_8_4 y z w b u)*(d1_0_2 y z w b u))+(((d0_8_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_8_6 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_6_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_6_5 y z w b u))+((d2_2_2 y z w b u)*(d3_6_4 y z w b u))))+((((d2_3_0 y z w b u)*(d3_5_6 y z w b u))+((d2_3_1 y z w b u)*(d3_5_5 y z w b u)))+((d2_4_0 y z w b u)*(d3_4_6 y z w b u)))))+((-1)*(d4_8_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_6,d0_4_6,d0_5_5,d0_5_6,d0_6_4,d0_6_5,d0_6_6,d0_7_4,d0_7_5,d0_7_6,d0_8_4,d0_8_5,d0_8_6,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_4_6,d3_5_5,d3_5_6,d3_6_4,d3_6_5,d3_6_6,d4_8_6]
  ring
#print axioms coefficient_8_6
compact_certificate_declaration theorem coefficient_8_7 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[7]?=some 0 := by
  change some (((((((d0_3_7 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_4_7 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_5_6 y z w b u)*(d1_3_1 y z w b u))+(((d0_5_7 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_6_5 y z w b u)*(d1_2_2 y z w b u))+(((d0_6_6 y z w b u)*(d1_2_1 y z w b u))+(((d0_6_7 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_7_5 y z w b u)*(d1_1_2 y z w b u))+(((d0_7_6 y z w b u)*(d1_1_1 y z w b u))+(((d0_7_7 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_8_5 y z w b u)*(d1_0_2 y z w b u))+((d0_8_6 y z w b u)*(d1_0_1 y z w b u))))))))+((((d2_2_0 y z w b u)*(d3_6_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_6_6 y z w b u))+((d2_2_2 y z w b u)*(d3_6_5 y z w b u))))+((((d2_3_0 y z w b u)*(d3_5_7 y z w b u))+((d2_3_1 y z w b u)*(d3_5_6 y z w b u)))+((d2_4_0 y z w b u)*(d3_4_7 y z w b u)))))+((-1)*(d4_8_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_3_7,d0_4_7,d0_5_6,d0_5_7,d0_6_5,d0_6_6,d0_6_7,d0_7_5,d0_7_6,d0_7_7,d0_8_5,d0_8_6,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_4_7,d3_5_6,d3_5_7,d3_6_5,d3_6_6,d3_6_7,d4_8_7]
  ring
#print axioms coefficient_8_7

compact_certificate_declaration theorem coefficient_8_8 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[8]?=some 0 := by
  change some ((((((d0_5_7 y z w b u)*(d1_3_1 y z w b u))+((((d0_6_6 y z w b u)*(d1_2_2 y z w b u))+((d0_6_7 y z w b u)*(d1_2_1 y z w b u)))+((((d0_7_6 y z w b u)*(d1_1_2 y z w b u))+((d0_7_7 y z w b u)*(d1_1_1 y z w b u)))+((d0_8_6 y z w b u)*(d1_0_2 y z w b u)))))+((((d2_2_1 y z w b u)*(d3_6_7 y z w b u))+((d2_2_2 y z w b u)*(d3_6_6 y z w b u)))+((d2_3_1 y z w b u)*(d3_5_7 y z w b u))))+((-1)*(d4_8_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_5_7,d0_6_6,d0_6_7,d0_7_6,d0_7_7,d0_8_6,d1_0_2,d1_1_1,d1_1_2,d1_2_1,d1_2_2,d1_3_1,d2_2_1,d2_2_2,d2_3_1,d3_5_7,d3_6_6,d3_6_7,d4_8_8]
  ring
#print axioms coefficient_8_8
compact_certificate_declaration theorem coefficient_8_9 (y z w b u : ℂ) :
    (innerCertificate8 y z w b u)[9]?=some 0 := by
  change some ((((((d0_6_7 y z w b u)*(d1_2_2 y z w b u))+((d0_7_7 y z w b u)*(d1_1_2 y z w b u)))+((d2_2_2 y z w b u)*(d3_6_7 y z w b u)))+((-1)*(d4_8_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_6_7,d0_7_7,d1_1_2,d1_2_2,d2_2_2,d3_6_7,d4_8_9]
  ring
#print axioms coefficient_8_9

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_9 (y z w b u : ℂ) : (innerCertificate9 y z w b u).length=10 := by
  norm_num [innerCertificate9,add,multiply,scale,inner0_4,inner0_5,inner0_6,inner0_7,inner0_8,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner1_4,inner1_5,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner3_5,inner3_6,inner3_7,inner3_8,inner3_9,inner4_9]
compact_certificate_declaration theorem inner_eval_9 (y z w a b u : ℂ) :
    evaluate a (innerCertificate9 y z w b u)=(((((c0_4 y z w a b u)*(c1_5 y z w a b u))+(((c0_5 y z w a b u)*(c1_4 y z w a b u))+(((c0_6 y z w a b u)*(c1_3 y z w a b u))+(((c0_7 y z w a b u)*(c1_2 y z w a b u))+(((c0_8 y z w a b u)*(c1_1 y z w a b u))+(((c0_9 y z w a b u)*(c1_0 y z w a b u))+0))))))+(((c2_0 y z w a b u)*(c3_9 y z w a b u))+(((c2_1 y z w a b u)*(c3_8 y z w a b u))+(((c2_2 y z w a b u)*(c3_7 y z w a b u))+(((c2_3 y z w a b u)*(c3_6 y z w a b u))+((c2_4 y z w a b u)*(c3_5 y z w a b u)))))))+((-1)*(c4_9 y z w a b u))) := by
  simp only [innerCertificate9,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_4,c0_5,c0_6,c0_7,c0_8,c0_9,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_0,c2_1,c2_2,c2_3,c2_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_9]
#print axioms inner_eval_9

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_9_0 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[0]?=some 0 := by
  change some (((((((d0_4_0 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_5_0 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_6_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_7_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_8_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_9_0 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_7_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_6_0 y z w b u))+0)+(((d2_4_0 y z w b u)*(d3_5_0 y z w b u))+0))))+(((-1)*(d4_9_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_0,d0_5_0,d0_6_0,d0_7_0,d0_8_0,d0_9_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d1_4_0,d1_5_0,d2_2_0,d2_3_0,d2_4_0,d3_5_0,d3_6_0,d3_7_0,d4_9_0]
  ring
#print axioms coefficient_9_0

compact_certificate_declaration theorem coefficient_9_1 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[1]?=some 0 := by
  change some (((((((d0_4_1 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_5_1 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_6_0 y z w b u)*(d1_3_1 y z w b u))+(((d0_6_1 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_7_0 y z w b u)*(d1_2_1 y z w b u))+(((d0_7_1 y z w b u)*(d1_2_0 y z w b u))+0))+((((d0_8_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_8_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_9_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_9_1 y z w b u)*(d1_0_0 y z w b u))+0)))))))+((((d2_2_0 y z w b u)*(d3_7_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_7_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_6_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_6_0 y z w b u))+0))+((d2_4_0 y z w b u)*(d3_5_1 y z w b u)))))+((-1)*(d4_9_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_1,d0_5_1,d0_6_0,d0_6_1,d0_7_0,d0_7_1,d0_8_0,d0_8_1,d0_9_0,d0_9_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_2_1,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d3_5_1,d3_6_0,d3_6_1,d3_7_0,d3_7_1,d4_9_1]
  ring
#print axioms coefficient_9_1

compact_certificate_declaration theorem coefficient_9_2 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[2]?=some 0 := by
  change some (((((((d0_4_2 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_5_2 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_6_1 y z w b u)*(d1_3_1 y z w b u))+(((d0_6_2 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_7_0 y z w b u)*(d1_2_2 y z w b u))+(((d0_7_1 y z w b u)*(d1_2_1 y z w b u))+(((d0_7_2 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_8_0 y z w b u)*(d1_1_2 y z w b u))+(((d0_8_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_8_2 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_9_0 y z w b u)*(d1_0_2 y z w b u))+(((d0_9_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_9_2 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_7_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_7_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_7_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_6_2 y z w b u))+((d2_3_1 y z w b u)*(d3_6_1 y z w b u)))+((d2_4_0 y z w b u)*(d3_5_2 y z w b u)))))+((-1)*(d4_9_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_2,d0_5_2,d0_6_1,d0_6_2,d0_7_0,d0_7_1,d0_7_2,d0_8_0,d0_8_1,d0_8_2,d0_9_0,d0_9_1,d0_9_2,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_5_2,d3_6_1,d3_6_2,d3_7_0,d3_7_1,d3_7_2,d4_9_2]
  ring
#print axioms coefficient_9_2

compact_certificate_declaration theorem coefficient_9_3 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[3]?=some 0 := by
  change some (((((((d0_4_3 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_5_3 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_6_2 y z w b u)*(d1_3_1 y z w b u))+(((d0_6_3 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_7_1 y z w b u)*(d1_2_2 y z w b u))+(((d0_7_2 y z w b u)*(d1_2_1 y z w b u))+(((d0_7_3 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_8_1 y z w b u)*(d1_1_2 y z w b u))+(((d0_8_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_8_3 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_9_1 y z w b u)*(d1_0_2 y z w b u))+(((d0_9_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_9_3 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_7_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_7_2 y z w b u))+((d2_2_2 y z w b u)*(d3_7_1 y z w b u))))+((((d2_3_0 y z w b u)*(d3_6_3 y z w b u))+((d2_3_1 y z w b u)*(d3_6_2 y z w b u)))+((d2_4_0 y z w b u)*(d3_5_3 y z w b u)))))+((-1)*(d4_9_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_3,d0_5_3,d0_6_2,d0_6_3,d0_7_1,d0_7_2,d0_7_3,d0_8_1,d0_8_2,d0_8_3,d0_9_1,d0_9_2,d0_9_3,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_5_3,d3_6_2,d3_6_3,d3_7_1,d3_7_2,d3_7_3,d4_9_3]
  ring
#print axioms coefficient_9_3

compact_certificate_declaration theorem coefficient_9_4 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[4]?=some 0 := by
  change some (((((((d0_4_4 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_5_4 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_6_3 y z w b u)*(d1_3_1 y z w b u))+(((d0_6_4 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_7_2 y z w b u)*(d1_2_2 y z w b u))+(((d0_7_3 y z w b u)*(d1_2_1 y z w b u))+(((d0_7_4 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_8_2 y z w b u)*(d1_1_2 y z w b u))+(((d0_8_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_8_4 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_9_2 y z w b u)*(d1_0_2 y z w b u))+(((d0_9_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_9_4 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_7_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_7_3 y z w b u))+((d2_2_2 y z w b u)*(d3_7_2 y z w b u))))+((((d2_3_0 y z w b u)*(d3_6_4 y z w b u))+((d2_3_1 y z w b u)*(d3_6_3 y z w b u)))+((d2_4_0 y z w b u)*(d3_5_4 y z w b u)))))+((-1)*(d4_9_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_4,d0_5_4,d0_6_3,d0_6_4,d0_7_2,d0_7_3,d0_7_4,d0_8_2,d0_8_3,d0_8_4,d0_9_2,d0_9_3,d0_9_4,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_5_4,d3_6_3,d3_6_4,d3_7_2,d3_7_3,d3_7_4,d4_9_4]
  ring
#print axioms coefficient_9_4

compact_certificate_declaration theorem coefficient_9_5 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[5]?=some 0 := by
  change some (((((((d0_4_5 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_5_5 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_6_4 y z w b u)*(d1_3_1 y z w b u))+(((d0_6_5 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_7_3 y z w b u)*(d1_2_2 y z w b u))+(((d0_7_4 y z w b u)*(d1_2_1 y z w b u))+(((d0_7_5 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_8_3 y z w b u)*(d1_1_2 y z w b u))+(((d0_8_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_8_5 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_9_3 y z w b u)*(d1_0_2 y z w b u))+(((d0_9_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_9_5 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_7_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_7_4 y z w b u))+((d2_2_2 y z w b u)*(d3_7_3 y z w b u))))+((((d2_3_0 y z w b u)*(d3_6_5 y z w b u))+((d2_3_1 y z w b u)*(d3_6_4 y z w b u)))+((d2_4_0 y z w b u)*(d3_5_5 y z w b u)))))+((-1)*(d4_9_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_5,d0_5_5,d0_6_4,d0_6_5,d0_7_3,d0_7_4,d0_7_5,d0_8_3,d0_8_4,d0_8_5,d0_9_3,d0_9_4,d0_9_5,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_5_5,d3_6_4,d3_6_5,d3_7_3,d3_7_4,d3_7_5,d4_9_5]
  ring
#print axioms coefficient_9_5
compact_certificate_declaration theorem coefficient_9_6 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[6]?=some 0 := by
  change some (((((((d0_4_6 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_5_6 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_6_5 y z w b u)*(d1_3_1 y z w b u))+(((d0_6_6 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_7_4 y z w b u)*(d1_2_2 y z w b u))+(((d0_7_5 y z w b u)*(d1_2_1 y z w b u))+(((d0_7_6 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_8_4 y z w b u)*(d1_1_2 y z w b u))+(((d0_8_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_8_6 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_9_4 y z w b u)*(d1_0_2 y z w b u))+(((d0_9_5 y z w b u)*(d1_0_1 y z w b u))+(((d0_9_6 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_7_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_7_5 y z w b u))+((d2_2_2 y z w b u)*(d3_7_4 y z w b u))))+((((d2_3_0 y z w b u)*(d3_6_6 y z w b u))+((d2_3_1 y z w b u)*(d3_6_5 y z w b u)))+((d2_4_0 y z w b u)*(d3_5_6 y z w b u)))))+((-1)*(d4_9_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_6,d0_5_6,d0_6_5,d0_6_6,d0_7_4,d0_7_5,d0_7_6,d0_8_4,d0_8_5,d0_8_6,d0_9_4,d0_9_5,d0_9_6,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_5_6,d3_6_5,d3_6_6,d3_7_4,d3_7_5,d3_7_6,d4_9_6]
  ring
#print axioms coefficient_9_6
compact_certificate_declaration theorem coefficient_9_7 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[7]?=some 0 := by
  change some (((((((d0_4_7 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_5_7 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_6_6 y z w b u)*(d1_3_1 y z w b u))+(((d0_6_7 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_7_5 y z w b u)*(d1_2_2 y z w b u))+(((d0_7_6 y z w b u)*(d1_2_1 y z w b u))+(((d0_7_7 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_8_5 y z w b u)*(d1_1_2 y z w b u))+((d0_8_6 y z w b u)*(d1_1_1 y z w b u)))+(((d0_9_5 y z w b u)*(d1_0_2 y z w b u))+((d0_9_6 y z w b u)*(d1_0_1 y z w b u))))))))+((((d2_2_0 y z w b u)*(d3_7_7 y z w b u))+(((d2_2_1 y z w b u)*(d3_7_6 y z w b u))+((d2_2_2 y z w b u)*(d3_7_5 y z w b u))))+((((d2_3_0 y z w b u)*(d3_6_7 y z w b u))+((d2_3_1 y z w b u)*(d3_6_6 y z w b u)))+((d2_4_0 y z w b u)*(d3_5_7 y z w b u)))))+((-1)*(d4_9_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_4_7,d0_5_7,d0_6_6,d0_6_7,d0_7_5,d0_7_6,d0_7_7,d0_8_5,d0_8_6,d0_9_5,d0_9_6,d1_0_1,d1_0_2,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_5_7,d3_6_6,d3_6_7,d3_7_5,d3_7_6,d3_7_7,d4_9_7]
  ring
#print axioms coefficient_9_7

compact_certificate_declaration theorem coefficient_9_8 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[8]?=some 0 := by
  change some ((((((d0_6_7 y z w b u)*(d1_3_1 y z w b u))+((((d0_7_6 y z w b u)*(d1_2_2 y z w b u))+((d0_7_7 y z w b u)*(d1_2_1 y z w b u)))+(((d0_8_6 y z w b u)*(d1_1_2 y z w b u))+((d0_9_6 y z w b u)*(d1_0_2 y z w b u)))))+((((d2_2_1 y z w b u)*(d3_7_7 y z w b u))+((d2_2_2 y z w b u)*(d3_7_6 y z w b u)))+((d2_3_1 y z w b u)*(d3_6_7 y z w b u))))+((-1)*(d4_9_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_6_7,d0_7_6,d0_7_7,d0_8_6,d0_9_6,d1_0_2,d1_1_2,d1_2_1,d1_2_2,d1_3_1,d2_2_1,d2_2_2,d2_3_1,d3_6_7,d3_7_6,d3_7_7,d4_9_8]
  ring
#print axioms coefficient_9_8
compact_certificate_declaration theorem coefficient_9_9 (y z w b u : ℂ) :
    (innerCertificate9 y z w b u)[9]?=some 0 := by
  change some (((((d0_7_7 y z w b u)*(d1_2_2 y z w b u))+((d2_2_2 y z w b u)*(d3_7_7 y z w b u)))+((-1)*(d4_9_9 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_7_7,d1_2_2,d2_2_2,d3_7_7,d4_9_9]
  ring
#print axioms coefficient_9_9

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_10 (y z w b u : ℂ) : (innerCertificate10 y z w b u).length=9 := by
  norm_num [innerCertificate10,add,multiply,scale,inner0_10,inner0_5,inner0_6,inner0_7,inner0_8,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner1_4,inner1_5,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner3_10,inner3_6,inner3_7,inner3_8,inner3_9,inner4_10]
compact_certificate_declaration theorem inner_eval_10 (y z w a b u : ℂ) :
    evaluate a (innerCertificate10 y z w b u)=(((((c0_5 y z w a b u)*(c1_5 y z w a b u))+(((c0_6 y z w a b u)*(c1_4 y z w a b u))+(((c0_7 y z w a b u)*(c1_3 y z w a b u))+(((c0_8 y z w a b u)*(c1_2 y z w a b u))+(((c0_9 y z w a b u)*(c1_1 y z w a b u))+(((c0_10 y z w a b u)*(c1_0 y z w a b u))+0))))))+(((c2_0 y z w a b u)*(c3_10 y z w a b u))+(((c2_1 y z w a b u)*(c3_9 y z w a b u))+(((c2_2 y z w a b u)*(c3_8 y z w a b u))+(((c2_3 y z w a b u)*(c3_7 y z w a b u))+((c2_4 y z w a b u)*(c3_6 y z w a b u)))))))+((-1)*(c4_10 y z w a b u))) := by
  simp only [innerCertificate10,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_10,c0_5,c0_6,c0_7,c0_8,c0_9,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_0,c2_1,c2_2,c2_3,c2_4,c3_10,c3_6,c3_7,c3_8,c3_9,c4_10]
#print axioms inner_eval_10

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_10_0 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[0]?=some 0 := by
  change some (((((((d0_5_0 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_6_0 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_7_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_8_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_9_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_10_0 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_8_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_7_0 y z w b u))+0)+(((d2_4_0 y z w b u)*(d3_6_0 y z w b u))+0))))+(((-1)*(d4_10_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_5_0,d0_6_0,d0_7_0,d0_8_0,d0_9_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d1_4_0,d1_5_0,d2_2_0,d2_3_0,d2_4_0,d3_6_0,d3_7_0,d3_8_0,d4_10_0]
  ring
#print axioms coefficient_10_0

compact_certificate_declaration theorem coefficient_10_1 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[1]?=some 0 := by
  change some (((((((d0_5_1 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_6_1 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_7_0 y z w b u)*(d1_3_1 y z w b u))+(((d0_7_1 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_8_0 y z w b u)*(d1_2_1 y z w b u))+(((d0_8_1 y z w b u)*(d1_2_0 y z w b u))+0))+((((d0_9_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_9_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_10_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_10_1 y z w b u)*(d1_0_0 y z w b u))+0)))))))+((((d2_2_0 y z w b u)*(d3_8_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_8_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_7_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_7_0 y z w b u))+0))+((d2_4_0 y z w b u)*(d3_6_1 y z w b u)))))+((-1)*(d4_10_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_10_1,d0_5_1,d0_6_1,d0_7_0,d0_7_1,d0_8_0,d0_8_1,d0_9_0,d0_9_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_2_1,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d3_6_1,d3_7_0,d3_7_1,d3_8_0,d3_8_1,d4_10_1]
  ring
#print axioms coefficient_10_1

compact_certificate_declaration theorem coefficient_10_2 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[2]?=some 0 := by
  change some (((((((d0_5_2 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_6_2 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_7_1 y z w b u)*(d1_3_1 y z w b u))+(((d0_7_2 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_8_0 y z w b u)*(d1_2_2 y z w b u))+(((d0_8_1 y z w b u)*(d1_2_1 y z w b u))+(((d0_8_2 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_9_0 y z w b u)*(d1_1_2 y z w b u))+(((d0_9_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_9_2 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_10_0 y z w b u)*(d1_0_2 y z w b u))+(((d0_10_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_10_2 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_8_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_8_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_8_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_7_2 y z w b u))+((d2_3_1 y z w b u)*(d3_7_1 y z w b u)))+((d2_4_0 y z w b u)*(d3_6_2 y z w b u)))))+((-1)*(d4_10_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_10_1,d0_10_2,d0_5_2,d0_6_2,d0_7_1,d0_7_2,d0_8_0,d0_8_1,d0_8_2,d0_9_0,d0_9_1,d0_9_2,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_6_2,d3_7_1,d3_7_2,d3_8_0,d3_8_1,d3_8_2,d4_10_2]
  ring
#print axioms coefficient_10_2

compact_certificate_declaration theorem coefficient_10_3 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[3]?=some 0 := by
  change some (((((((d0_5_3 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_6_3 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_7_2 y z w b u)*(d1_3_1 y z w b u))+(((d0_7_3 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_8_1 y z w b u)*(d1_2_2 y z w b u))+(((d0_8_2 y z w b u)*(d1_2_1 y z w b u))+(((d0_8_3 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_9_1 y z w b u)*(d1_1_2 y z w b u))+(((d0_9_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_9_3 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_10_1 y z w b u)*(d1_0_2 y z w b u))+(((d0_10_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_10_3 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_8_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_8_2 y z w b u))+((d2_2_2 y z w b u)*(d3_8_1 y z w b u))))+((((d2_3_0 y z w b u)*(d3_7_3 y z w b u))+((d2_3_1 y z w b u)*(d3_7_2 y z w b u)))+((d2_4_0 y z w b u)*(d3_6_3 y z w b u)))))+((-1)*(d4_10_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_1,d0_10_2,d0_10_3,d0_5_3,d0_6_3,d0_7_2,d0_7_3,d0_8_1,d0_8_2,d0_8_3,d0_9_1,d0_9_2,d0_9_3,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_6_3,d3_7_2,d3_7_3,d3_8_1,d3_8_2,d3_8_3,d4_10_3]
  ring
#print axioms coefficient_10_3

compact_certificate_declaration theorem coefficient_10_4 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[4]?=some 0 := by
  change some (((((((d0_5_4 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_6_4 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_7_3 y z w b u)*(d1_3_1 y z w b u))+(((d0_7_4 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_8_2 y z w b u)*(d1_2_2 y z w b u))+(((d0_8_3 y z w b u)*(d1_2_1 y z w b u))+(((d0_8_4 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_9_2 y z w b u)*(d1_1_2 y z w b u))+(((d0_9_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_9_4 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_10_2 y z w b u)*(d1_0_2 y z w b u))+(((d0_10_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_10_4 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_8_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_8_3 y z w b u))+((d2_2_2 y z w b u)*(d3_8_2 y z w b u))))+((((d2_3_0 y z w b u)*(d3_7_4 y z w b u))+((d2_3_1 y z w b u)*(d3_7_3 y z w b u)))+((d2_4_0 y z w b u)*(d3_6_4 y z w b u)))))+((-1)*(d4_10_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_2,d0_10_3,d0_10_4,d0_5_4,d0_6_4,d0_7_3,d0_7_4,d0_8_2,d0_8_3,d0_8_4,d0_9_2,d0_9_3,d0_9_4,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_6_4,d3_7_3,d3_7_4,d3_8_2,d3_8_3,d3_8_4,d4_10_4]
  ring
#print axioms coefficient_10_4
compact_certificate_declaration theorem coefficient_10_5 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[5]?=some 0 := by
  change some (((((((d0_5_5 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_6_5 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_7_4 y z w b u)*(d1_3_1 y z w b u))+(((d0_7_5 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_8_3 y z w b u)*(d1_2_2 y z w b u))+(((d0_8_4 y z w b u)*(d1_2_1 y z w b u))+(((d0_8_5 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_9_3 y z w b u)*(d1_1_2 y z w b u))+(((d0_9_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_9_5 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_10_3 y z w b u)*(d1_0_2 y z w b u))+(((d0_10_4 y z w b u)*(d1_0_1 y z w b u))+(((d0_10_5 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_8_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_8_4 y z w b u))+((d2_2_2 y z w b u)*(d3_8_3 y z w b u))))+((((d2_3_0 y z w b u)*(d3_7_5 y z w b u))+((d2_3_1 y z w b u)*(d3_7_4 y z w b u)))+((d2_4_0 y z w b u)*(d3_6_5 y z w b u)))))+((-1)*(d4_10_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_3,d0_10_4,d0_10_5,d0_5_5,d0_6_5,d0_7_4,d0_7_5,d0_8_3,d0_8_4,d0_8_5,d0_9_3,d0_9_4,d0_9_5,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_6_5,d3_7_4,d3_7_5,d3_8_3,d3_8_4,d3_8_5,d4_10_5]
  ring
#print axioms coefficient_10_5

compact_certificate_declaration theorem coefficient_10_6 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[6]?=some 0 := by
  change some (((((((d0_5_6 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_6_6 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_7_5 y z w b u)*(d1_3_1 y z w b u))+(((d0_7_6 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_8_4 y z w b u)*(d1_2_2 y z w b u))+(((d0_8_5 y z w b u)*(d1_2_1 y z w b u))+(((d0_8_6 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_9_4 y z w b u)*(d1_1_2 y z w b u))+(((d0_9_5 y z w b u)*(d1_1_1 y z w b u))+(((d0_9_6 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_10_4 y z w b u)*(d1_0_2 y z w b u))+((d0_10_5 y z w b u)*(d1_0_1 y z w b u))))))))+((((d2_2_0 y z w b u)*(d3_8_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_8_5 y z w b u))+((d2_2_2 y z w b u)*(d3_8_4 y z w b u))))+((((d2_3_0 y z w b u)*(d3_7_6 y z w b u))+((d2_3_1 y z w b u)*(d3_7_5 y z w b u)))+((d2_4_0 y z w b u)*(d3_6_6 y z w b u)))))+((-1)*(d4_10_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_4,d0_10_5,d0_5_6,d0_6_6,d0_7_5,d0_7_6,d0_8_4,d0_8_5,d0_8_6,d0_9_4,d0_9_5,d0_9_6,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_6_6,d3_7_5,d3_7_6,d3_8_4,d3_8_5,d3_8_6,d4_10_6]
  ring
#print axioms coefficient_10_6
compact_certificate_declaration theorem coefficient_10_7 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[7]?=some 0 := by
  change some (((((((d0_5_7 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_6_7 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_7_6 y z w b u)*(d1_3_1 y z w b u))+(((d0_7_7 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_8_5 y z w b u)*(d1_2_2 y z w b u))+((d0_8_6 y z w b u)*(d1_2_1 y z w b u)))+((((d0_9_5 y z w b u)*(d1_1_2 y z w b u))+((d0_9_6 y z w b u)*(d1_1_1 y z w b u)))+((d0_10_5 y z w b u)*(d1_0_2 y z w b u)))))))+((((d2_2_1 y z w b u)*(d3_8_6 y z w b u))+((d2_2_2 y z w b u)*(d3_8_5 y z w b u)))+((((d2_3_0 y z w b u)*(d3_7_7 y z w b u))+((d2_3_1 y z w b u)*(d3_7_6 y z w b u)))+((d2_4_0 y z w b u)*(d3_6_7 y z w b u)))))+((-1)*(d4_10_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_5,d0_5_7,d0_6_7,d0_7_6,d0_7_7,d0_8_5,d0_8_6,d0_9_5,d0_9_6,d1_0_2,d1_1_1,d1_1_2,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_6_7,d3_7_6,d3_7_7,d3_8_5,d3_8_6,d4_10_7]
  ring
#print axioms coefficient_10_7
compact_certificate_declaration theorem coefficient_10_8 (y z w b u : ℂ) :
    (innerCertificate10 y z w b u)[8]?=some 0 := by
  change some ((((((d0_7_7 y z w b u)*(d1_3_1 y z w b u))+(((d0_8_6 y z w b u)*(d1_2_2 y z w b u))+((d0_9_6 y z w b u)*(d1_1_2 y z w b u))))+(((d2_2_2 y z w b u)*(d3_8_6 y z w b u))+((d2_3_1 y z w b u)*(d3_7_7 y z w b u))))+((-1)*(d4_10_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_7_7,d0_8_6,d0_9_6,d1_1_2,d1_2_2,d1_3_1,d2_2_2,d2_3_1,d3_7_7,d3_8_6,d4_10_8]
  ring
#print axioms coefficient_10_8

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_11 (y z w b u : ℂ) : (innerCertificate11 y z w b u).length=9 := by
  norm_num [innerCertificate11,add,multiply,scale,inner0_10,inner0_11,inner0_6,inner0_7,inner0_8,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner1_4,inner1_5,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner3_10,inner3_11,inner3_7,inner3_8,inner3_9,inner4_11]
compact_certificate_declaration theorem inner_eval_11 (y z w a b u : ℂ) :
    evaluate a (innerCertificate11 y z w b u)=(((((c0_6 y z w a b u)*(c1_5 y z w a b u))+(((c0_7 y z w a b u)*(c1_4 y z w a b u))+(((c0_8 y z w a b u)*(c1_3 y z w a b u))+(((c0_9 y z w a b u)*(c1_2 y z w a b u))+(((c0_10 y z w a b u)*(c1_1 y z w a b u))+(((c0_11 y z w a b u)*(c1_0 y z w a b u))+0))))))+(((c2_0 y z w a b u)*(c3_11 y z w a b u))+(((c2_1 y z w a b u)*(c3_10 y z w a b u))+(((c2_2 y z w a b u)*(c3_9 y z w a b u))+(((c2_3 y z w a b u)*(c3_8 y z w a b u))+((c2_4 y z w a b u)*(c3_7 y z w a b u)))))))+((-1)*(c4_11 y z w a b u))) := by
  simp only [innerCertificate11,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_10,c0_11,c0_6,c0_7,c0_8,c0_9,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_0,c2_1,c2_2,c2_3,c2_4,c3_10,c3_11,c3_7,c3_8,c3_9,c4_11]
#print axioms inner_eval_11

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_11_0 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[0]?=some 0 := by
  change some (((((((d0_6_0 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_7_0 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_8_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_9_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_10_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_11_0 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_9_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_8_0 y z w b u))+0)+(((d2_4_0 y z w b u)*(d3_7_0 y z w b u))+0))))+(((-1)*(d4_11_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_11_0,d0_6_0,d0_7_0,d0_8_0,d0_9_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d1_4_0,d1_5_0,d2_2_0,d2_3_0,d2_4_0,d3_7_0,d3_8_0,d3_9_0,d4_11_0]
  ring
#print axioms coefficient_11_0

compact_certificate_declaration theorem coefficient_11_1 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[1]?=some 0 := by
  change some (((((((d0_6_1 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_7_1 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_8_0 y z w b u)*(d1_3_1 y z w b u))+(((d0_8_1 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_9_0 y z w b u)*(d1_2_1 y z w b u))+(((d0_9_1 y z w b u)*(d1_2_0 y z w b u))+0))+((((d0_10_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_10_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_11_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_11_1 y z w b u)*(d1_0_0 y z w b u))+0)))))))+((((d2_2_0 y z w b u)*(d3_9_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_9_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_8_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_8_0 y z w b u))+0))+((d2_4_0 y z w b u)*(d3_7_1 y z w b u)))))+((-1)*(d4_11_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_10_1,d0_11_0,d0_11_1,d0_6_1,d0_7_1,d0_8_0,d0_8_1,d0_9_0,d0_9_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_2_1,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d3_7_1,d3_8_0,d3_8_1,d3_9_0,d3_9_1,d4_11_1]
  ring
#print axioms coefficient_11_1

compact_certificate_declaration theorem coefficient_11_2 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[2]?=some 0 := by
  change some (((((((d0_6_2 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_7_2 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_8_1 y z w b u)*(d1_3_1 y z w b u))+(((d0_8_2 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_9_0 y z w b u)*(d1_2_2 y z w b u))+(((d0_9_1 y z w b u)*(d1_2_1 y z w b u))+(((d0_9_2 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_10_0 y z w b u)*(d1_1_2 y z w b u))+(((d0_10_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_10_2 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_11_0 y z w b u)*(d1_0_2 y z w b u))+(((d0_11_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_11_2 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_9_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_9_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_9_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_8_2 y z w b u))+((d2_3_1 y z w b u)*(d3_8_1 y z w b u)))+((d2_4_0 y z w b u)*(d3_7_2 y z w b u)))))+((-1)*(d4_11_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_10_1,d0_10_2,d0_11_0,d0_11_1,d0_11_2,d0_6_2,d0_7_2,d0_8_1,d0_8_2,d0_9_0,d0_9_1,d0_9_2,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_7_2,d3_8_1,d3_8_2,d3_9_0,d3_9_1,d3_9_2,d4_11_2]
  ring
#print axioms coefficient_11_2

compact_certificate_declaration theorem coefficient_11_3 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[3]?=some 0 := by
  change some (((((((d0_6_3 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_7_3 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_8_2 y z w b u)*(d1_3_1 y z w b u))+(((d0_8_3 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_9_1 y z w b u)*(d1_2_2 y z w b u))+(((d0_9_2 y z w b u)*(d1_2_1 y z w b u))+(((d0_9_3 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_10_1 y z w b u)*(d1_1_2 y z w b u))+(((d0_10_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_10_3 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_11_1 y z w b u)*(d1_0_2 y z w b u))+(((d0_11_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_11_3 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_9_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_9_2 y z w b u))+((d2_2_2 y z w b u)*(d3_9_1 y z w b u))))+((((d2_3_0 y z w b u)*(d3_8_3 y z w b u))+((d2_3_1 y z w b u)*(d3_8_2 y z w b u)))+((d2_4_0 y z w b u)*(d3_7_3 y z w b u)))))+((-1)*(d4_11_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_1,d0_10_2,d0_10_3,d0_11_1,d0_11_2,d0_11_3,d0_6_3,d0_7_3,d0_8_2,d0_8_3,d0_9_1,d0_9_2,d0_9_3,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_7_3,d3_8_2,d3_8_3,d3_9_1,d3_9_2,d3_9_3,d4_11_3]
  ring
#print axioms coefficient_11_3

compact_certificate_declaration theorem coefficient_11_4 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[4]?=some 0 := by
  change some (((((((d0_6_4 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_7_4 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_8_3 y z w b u)*(d1_3_1 y z w b u))+(((d0_8_4 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_9_2 y z w b u)*(d1_2_2 y z w b u))+(((d0_9_3 y z w b u)*(d1_2_1 y z w b u))+(((d0_9_4 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_10_2 y z w b u)*(d1_1_2 y z w b u))+(((d0_10_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_10_4 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_11_2 y z w b u)*(d1_0_2 y z w b u))+(((d0_11_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_11_4 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_9_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_9_3 y z w b u))+((d2_2_2 y z w b u)*(d3_9_2 y z w b u))))+((((d2_3_0 y z w b u)*(d3_8_4 y z w b u))+((d2_3_1 y z w b u)*(d3_8_3 y z w b u)))+((d2_4_0 y z w b u)*(d3_7_4 y z w b u)))))+((-1)*(d4_11_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_2,d0_10_3,d0_10_4,d0_11_2,d0_11_3,d0_11_4,d0_6_4,d0_7_4,d0_8_3,d0_8_4,d0_9_2,d0_9_3,d0_9_4,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_7_4,d3_8_3,d3_8_4,d3_9_2,d3_9_3,d3_9_4,d4_11_4]
  ring
#print axioms coefficient_11_4
compact_certificate_declaration theorem coefficient_11_5 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[5]?=some 0 := by
  change some (((((((d0_6_5 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_7_5 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_8_4 y z w b u)*(d1_3_1 y z w b u))+(((d0_8_5 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_9_3 y z w b u)*(d1_2_2 y z w b u))+(((d0_9_4 y z w b u)*(d1_2_1 y z w b u))+(((d0_9_5 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_10_3 y z w b u)*(d1_1_2 y z w b u))+(((d0_10_4 y z w b u)*(d1_1_1 y z w b u))+(((d0_10_5 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_11_3 y z w b u)*(d1_0_2 y z w b u))+((d0_11_4 y z w b u)*(d1_0_1 y z w b u))))))))+((((d2_2_0 y z w b u)*(d3_9_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_9_4 y z w b u))+((d2_2_2 y z w b u)*(d3_9_3 y z w b u))))+((((d2_3_0 y z w b u)*(d3_8_5 y z w b u))+((d2_3_1 y z w b u)*(d3_8_4 y z w b u)))+((d2_4_0 y z w b u)*(d3_7_5 y z w b u)))))+((-1)*(d4_11_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_3,d0_10_4,d0_10_5,d0_11_3,d0_11_4,d0_6_5,d0_7_5,d0_8_4,d0_8_5,d0_9_3,d0_9_4,d0_9_5,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_7_5,d3_8_4,d3_8_5,d3_9_3,d3_9_4,d3_9_5,d4_11_5]
  ring
#print axioms coefficient_11_5
compact_certificate_declaration theorem coefficient_11_6 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[6]?=some 0 := by
  change some (((((((d0_6_6 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_7_6 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_8_5 y z w b u)*(d1_3_1 y z w b u))+(((d0_8_6 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_9_4 y z w b u)*(d1_2_2 y z w b u))+(((d0_9_5 y z w b u)*(d1_2_1 y z w b u))+(((d0_9_6 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_10_4 y z w b u)*(d1_1_2 y z w b u))+((d0_10_5 y z w b u)*(d1_1_1 y z w b u)))+((d0_11_4 y z w b u)*(d1_0_2 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_9_6 y z w b u))+(((d2_2_1 y z w b u)*(d3_9_5 y z w b u))+((d2_2_2 y z w b u)*(d3_9_4 y z w b u))))+((((d2_3_0 y z w b u)*(d3_8_6 y z w b u))+((d2_3_1 y z w b u)*(d3_8_5 y z w b u)))+((d2_4_0 y z w b u)*(d3_7_6 y z w b u)))))+((-1)*(d4_11_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_4,d0_10_5,d0_11_4,d0_6_6,d0_7_6,d0_8_5,d0_8_6,d0_9_4,d0_9_5,d0_9_6,d1_0_2,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_7_6,d3_8_5,d3_8_6,d3_9_4,d3_9_5,d3_9_6,d4_11_6]
  ring
#print axioms coefficient_11_6

compact_certificate_declaration theorem coefficient_11_7 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[7]?=some 0 := by
  change some (((((((d0_6_7 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_7_7 y z w b u)*(d1_4_0 y z w b u))+0)+(((d0_8_6 y z w b u)*(d1_3_1 y z w b u))+((((d0_9_5 y z w b u)*(d1_2_2 y z w b u))+((d0_9_6 y z w b u)*(d1_2_1 y z w b u)))+((d0_10_5 y z w b u)*(d1_1_2 y z w b u))))))+((((d2_2_1 y z w b u)*(d3_9_6 y z w b u))+((d2_2_2 y z w b u)*(d3_9_5 y z w b u)))+(((d2_3_1 y z w b u)*(d3_8_6 y z w b u))+((d2_4_0 y z w b u)*(d3_7_7 y z w b u)))))+((-1)*(d4_11_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_5,d0_6_7,d0_7_7,d0_8_6,d0_9_5,d0_9_6,d1_1_2,d1_2_1,d1_2_2,d1_3_1,d1_4_0,d1_5_0,d2_2_1,d2_2_2,d2_3_1,d2_4_0,d3_7_7,d3_8_6,d3_9_5,d3_9_6,d4_11_7]
  ring
#print axioms coefficient_11_7
compact_certificate_declaration theorem coefficient_11_8 (y z w b u : ℂ) :
    (innerCertificate11 y z w b u)[8]?=some 0 := by
  change some (((((d0_9_6 y z w b u)*(d1_2_2 y z w b u))+((d2_2_2 y z w b u)*(d3_9_6 y z w b u)))+((-1)*(d4_11_8 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_9_6,d1_2_2,d2_2_2,d3_9_6,d4_11_8]
  ring
#print axioms coefficient_11_8

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_12 (y z w b u : ℂ) : (innerCertificate12 y z w b u).length=8 := by
  norm_num [innerCertificate12,add,multiply,scale,inner0_10,inner0_11,inner0_12,inner0_7,inner0_8,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner1_4,inner1_5,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner3_10,inner3_11,inner3_12,inner3_8,inner3_9,inner4_12]
compact_certificate_declaration theorem inner_eval_12 (y z w a b u : ℂ) :
    evaluate a (innerCertificate12 y z w b u)=(((((c0_7 y z w a b u)*(c1_5 y z w a b u))+(((c0_8 y z w a b u)*(c1_4 y z w a b u))+(((c0_9 y z w a b u)*(c1_3 y z w a b u))+(((c0_10 y z w a b u)*(c1_2 y z w a b u))+(((c0_11 y z w a b u)*(c1_1 y z w a b u))+(((c0_12 y z w a b u)*(c1_0 y z w a b u))+0))))))+(((c2_0 y z w a b u)*(c3_12 y z w a b u))+(((c2_1 y z w a b u)*(c3_11 y z w a b u))+(((c2_2 y z w a b u)*(c3_10 y z w a b u))+(((c2_3 y z w a b u)*(c3_9 y z w a b u))+((c2_4 y z w a b u)*(c3_8 y z w a b u)))))))+((-1)*(c4_12 y z w a b u))) := by
  simp only [innerCertificate12,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_10,c0_11,c0_12,c0_7,c0_8,c0_9,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_0,c2_1,c2_2,c2_3,c2_4,c3_10,c3_11,c3_12,c3_8,c3_9,c4_12]
#print axioms inner_eval_12

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_12_0 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[0]?=some 0 := by
  change some (((((((d0_7_0 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_8_0 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_9_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_10_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_11_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_12_0 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_10_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_9_0 y z w b u))+0)+(((d2_4_0 y z w b u)*(d3_8_0 y z w b u))+0))))+(((-1)*(d4_12_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_11_0,d0_12_0,d0_7_0,d0_8_0,d0_9_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d1_4_0,d1_5_0,d2_2_0,d2_3_0,d2_4_0,d3_10_0,d3_8_0,d3_9_0,d4_12_0]
  ring
#print axioms coefficient_12_0

compact_certificate_declaration theorem coefficient_12_1 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[1]?=some 0 := by
  change some (((((((d0_7_1 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_8_1 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_9_0 y z w b u)*(d1_3_1 y z w b u))+(((d0_9_1 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_10_0 y z w b u)*(d1_2_1 y z w b u))+(((d0_10_1 y z w b u)*(d1_2_0 y z w b u))+0))+((((d0_11_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_11_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_12_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_12_1 y z w b u)*(d1_0_0 y z w b u))+0)))))))+((((d2_2_0 y z w b u)*(d3_10_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_10_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_9_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_9_0 y z w b u))+0))+((d2_4_0 y z w b u)*(d3_8_1 y z w b u)))))+((-1)*(d4_12_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_10_1,d0_11_0,d0_11_1,d0_12_0,d0_12_1,d0_7_1,d0_8_1,d0_9_0,d0_9_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_2_1,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d3_10_0,d3_10_1,d3_8_1,d3_9_0,d3_9_1,d4_12_1]
  ring
#print axioms coefficient_12_1

compact_certificate_declaration theorem coefficient_12_2 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[2]?=some 0 := by
  change some (((((((d0_7_2 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_8_2 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_9_1 y z w b u)*(d1_3_1 y z w b u))+(((d0_9_2 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_10_0 y z w b u)*(d1_2_2 y z w b u))+(((d0_10_1 y z w b u)*(d1_2_1 y z w b u))+(((d0_10_2 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_11_0 y z w b u)*(d1_1_2 y z w b u))+(((d0_11_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_11_2 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_12_0 y z w b u)*(d1_0_2 y z w b u))+(((d0_12_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_12_2 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_10_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_10_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_10_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_9_2 y z w b u))+((d2_3_1 y z w b u)*(d3_9_1 y z w b u)))+((d2_4_0 y z w b u)*(d3_8_2 y z w b u)))))+((-1)*(d4_12_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_10_1,d0_10_2,d0_11_0,d0_11_1,d0_11_2,d0_12_0,d0_12_1,d0_12_2,d0_7_2,d0_8_2,d0_9_1,d0_9_2,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_10_0,d3_10_1,d3_10_2,d3_8_2,d3_9_1,d3_9_2,d4_12_2]
  ring
#print axioms coefficient_12_2

compact_certificate_declaration theorem coefficient_12_3 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[3]?=some 0 := by
  change some (((((((d0_7_3 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_8_3 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_9_2 y z w b u)*(d1_3_1 y z w b u))+(((d0_9_3 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_10_1 y z w b u)*(d1_2_2 y z w b u))+(((d0_10_2 y z w b u)*(d1_2_1 y z w b u))+(((d0_10_3 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_11_1 y z w b u)*(d1_1_2 y z w b u))+(((d0_11_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_11_3 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_12_1 y z w b u)*(d1_0_2 y z w b u))+(((d0_12_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_12_3 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_10_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_10_2 y z w b u))+((d2_2_2 y z w b u)*(d3_10_1 y z w b u))))+((((d2_3_0 y z w b u)*(d3_9_3 y z w b u))+((d2_3_1 y z w b u)*(d3_9_2 y z w b u)))+((d2_4_0 y z w b u)*(d3_8_3 y z w b u)))))+((-1)*(d4_12_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_1,d0_10_2,d0_10_3,d0_11_1,d0_11_2,d0_11_3,d0_12_1,d0_12_2,d0_12_3,d0_7_3,d0_8_3,d0_9_2,d0_9_3,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_10_1,d3_10_2,d3_10_3,d3_8_3,d3_9_2,d3_9_3,d4_12_3]
  ring
#print axioms coefficient_12_3
compact_certificate_declaration theorem coefficient_12_4 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[4]?=some 0 := by
  change some (((((((d0_7_4 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_8_4 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_9_3 y z w b u)*(d1_3_1 y z w b u))+(((d0_9_4 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_10_2 y z w b u)*(d1_2_2 y z w b u))+(((d0_10_3 y z w b u)*(d1_2_1 y z w b u))+(((d0_10_4 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_11_2 y z w b u)*(d1_1_2 y z w b u))+(((d0_11_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_11_4 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_12_2 y z w b u)*(d1_0_2 y z w b u))+(((d0_12_3 y z w b u)*(d1_0_1 y z w b u))+(((d0_12_4 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_10_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_10_3 y z w b u))+((d2_2_2 y z w b u)*(d3_10_2 y z w b u))))+((((d2_3_0 y z w b u)*(d3_9_4 y z w b u))+((d2_3_1 y z w b u)*(d3_9_3 y z w b u)))+((d2_4_0 y z w b u)*(d3_8_4 y z w b u)))))+((-1)*(d4_12_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_2,d0_10_3,d0_10_4,d0_11_2,d0_11_3,d0_11_4,d0_12_2,d0_12_3,d0_12_4,d0_7_4,d0_8_4,d0_9_3,d0_9_4,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_10_2,d3_10_3,d3_10_4,d3_8_4,d3_9_3,d3_9_4,d4_12_4]
  ring
#print axioms coefficient_12_4
compact_certificate_declaration theorem coefficient_12_5 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[5]?=some 0 := by
  change some (((((((d0_7_5 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_8_5 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_9_4 y z w b u)*(d1_3_1 y z w b u))+(((d0_9_5 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_10_3 y z w b u)*(d1_2_2 y z w b u))+(((d0_10_4 y z w b u)*(d1_2_1 y z w b u))+(((d0_10_5 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_11_3 y z w b u)*(d1_1_2 y z w b u))+((d0_11_4 y z w b u)*(d1_1_1 y z w b u)))+(((d0_12_3 y z w b u)*(d1_0_2 y z w b u))+((d0_12_4 y z w b u)*(d1_0_1 y z w b u))))))))+((((d2_2_0 y z w b u)*(d3_10_5 y z w b u))+(((d2_2_1 y z w b u)*(d3_10_4 y z w b u))+((d2_2_2 y z w b u)*(d3_10_3 y z w b u))))+((((d2_3_0 y z w b u)*(d3_9_5 y z w b u))+((d2_3_1 y z w b u)*(d3_9_4 y z w b u)))+((d2_4_0 y z w b u)*(d3_8_5 y z w b u)))))+((-1)*(d4_12_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_3,d0_10_4,d0_10_5,d0_11_3,d0_11_4,d0_12_3,d0_12_4,d0_7_5,d0_8_5,d0_9_4,d0_9_5,d1_0_1,d1_0_2,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_10_3,d3_10_4,d3_10_5,d3_8_5,d3_9_4,d3_9_5,d4_12_5]
  ring
#print axioms coefficient_12_5

compact_certificate_declaration theorem coefficient_12_6 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[6]?=some 0 := by
  change some (((((((d0_7_6 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_8_6 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_9_5 y z w b u)*(d1_3_1 y z w b u))+(((d0_9_6 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_10_4 y z w b u)*(d1_2_2 y z w b u))+((d0_10_5 y z w b u)*(d1_2_1 y z w b u)))+(((d0_11_4 y z w b u)*(d1_1_2 y z w b u))+((d0_12_4 y z w b u)*(d1_0_2 y z w b u)))))))+((((d2_2_1 y z w b u)*(d3_10_5 y z w b u))+((d2_2_2 y z w b u)*(d3_10_4 y z w b u)))+((((d2_3_0 y z w b u)*(d3_9_6 y z w b u))+((d2_3_1 y z w b u)*(d3_9_5 y z w b u)))+((d2_4_0 y z w b u)*(d3_8_6 y z w b u)))))+((-1)*(d4_12_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_4,d0_10_5,d0_11_4,d0_12_4,d0_7_6,d0_8_6,d0_9_5,d0_9_6,d1_0_2,d1_1_2,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_10_4,d3_10_5,d3_8_6,d3_9_5,d3_9_6,d4_12_6]
  ring
#print axioms coefficient_12_6
compact_certificate_declaration theorem coefficient_12_7 (y z w b u : ℂ) :
    (innerCertificate12 y z w b u)[7]?=some 0 := by
  change some (((((((d0_7_7 y z w b u)*(d1_5_0 y z w b u))+0)+(((d0_9_6 y z w b u)*(d1_3_1 y z w b u))+((d0_10_5 y z w b u)*(d1_2_2 y z w b u))))+(((d2_2_2 y z w b u)*(d3_10_5 y z w b u))+((d2_3_1 y z w b u)*(d3_9_6 y z w b u))))+((-1)*(d4_12_7 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_5,d0_7_7,d0_9_6,d1_2_2,d1_3_1,d1_5_0,d2_2_2,d2_3_1,d3_10_5,d3_9_6,d4_12_7]
  ring
#print axioms coefficient_12_7

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_13 (y z w b u : ℂ) : (innerCertificate13 y z w b u).length=7 := by
  norm_num [innerCertificate13,add,multiply,scale,inner0_10,inner0_11,inner0_12,inner0_13,inner0_8,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner1_4,inner1_5,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner3_10,inner3_11,inner3_12,inner3_13,inner3_9,inner4_13]
compact_certificate_declaration theorem inner_eval_13 (y z w a b u : ℂ) :
    evaluate a (innerCertificate13 y z w b u)=(((((c0_8 y z w a b u)*(c1_5 y z w a b u))+(((c0_9 y z w a b u)*(c1_4 y z w a b u))+(((c0_10 y z w a b u)*(c1_3 y z w a b u))+(((c0_11 y z w a b u)*(c1_2 y z w a b u))+(((c0_12 y z w a b u)*(c1_1 y z w a b u))+(((c0_13 y z w a b u)*(c1_0 y z w a b u))+0))))))+(((c2_0 y z w a b u)*(c3_13 y z w a b u))+(((c2_1 y z w a b u)*(c3_12 y z w a b u))+(((c2_2 y z w a b u)*(c3_11 y z w a b u))+(((c2_3 y z w a b u)*(c3_10 y z w a b u))+((c2_4 y z w a b u)*(c3_9 y z w a b u)))))))+((-1)*(c4_13 y z w a b u))) := by
  simp only [innerCertificate13,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_10,c0_11,c0_12,c0_13,c0_8,c0_9,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_0,c2_1,c2_2,c2_3,c2_4,c3_10,c3_11,c3_12,c3_13,c3_9,c4_13]
#print axioms inner_eval_13

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_13_0 (y z w b u : ℂ) :
    (innerCertificate13 y z w b u)[0]?=some 0 := by
  change some (((((((d0_8_0 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_9_0 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_10_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_11_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_12_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_13_0 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_11_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_10_0 y z w b u))+0)+(((d2_4_0 y z w b u)*(d3_9_0 y z w b u))+0))))+(((-1)*(d4_13_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_11_0,d0_12_0,d0_13_0,d0_8_0,d0_9_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d1_4_0,d1_5_0,d2_2_0,d2_3_0,d2_4_0,d3_10_0,d3_11_0,d3_9_0,d4_13_0]
  ring
#print axioms coefficient_13_0

compact_certificate_declaration theorem coefficient_13_1 (y z w b u : ℂ) :
    (innerCertificate13 y z w b u)[1]?=some 0 := by
  change some (((((((d0_8_1 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_9_1 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_10_0 y z w b u)*(d1_3_1 y z w b u))+(((d0_10_1 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_11_0 y z w b u)*(d1_2_1 y z w b u))+(((d0_11_1 y z w b u)*(d1_2_0 y z w b u))+0))+((((d0_12_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_12_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_13_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_13_1 y z w b u)*(d1_0_0 y z w b u))+0)))))))+((((d2_2_0 y z w b u)*(d3_11_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_11_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_10_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_10_0 y z w b u))+0))+((d2_4_0 y z w b u)*(d3_9_1 y z w b u)))))+((-1)*(d4_13_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_10_1,d0_11_0,d0_11_1,d0_12_0,d0_12_1,d0_13_0,d0_13_1,d0_8_1,d0_9_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_2_1,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d3_10_0,d3_10_1,d3_11_0,d3_11_1,d3_9_1,d4_13_1]
  ring
#print axioms coefficient_13_1

compact_certificate_declaration theorem coefficient_13_2 (y z w b u : ℂ) :
    (innerCertificate13 y z w b u)[2]?=some 0 := by
  change some (((((((d0_8_2 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_9_2 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_10_1 y z w b u)*(d1_3_1 y z w b u))+(((d0_10_2 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_11_0 y z w b u)*(d1_2_2 y z w b u))+(((d0_11_1 y z w b u)*(d1_2_1 y z w b u))+(((d0_11_2 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_12_0 y z w b u)*(d1_1_2 y z w b u))+(((d0_12_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_12_2 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_13_0 y z w b u)*(d1_0_2 y z w b u))+(((d0_13_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_13_2 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_11_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_11_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_11_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_10_2 y z w b u))+((d2_3_1 y z w b u)*(d3_10_1 y z w b u)))+((d2_4_0 y z w b u)*(d3_9_2 y z w b u)))))+((-1)*(d4_13_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_1,d0_10_2,d0_11_0,d0_11_1,d0_11_2,d0_12_0,d0_12_1,d0_12_2,d0_13_0,d0_13_1,d0_13_2,d0_8_2,d0_9_2,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_10_1,d3_10_2,d3_11_0,d3_11_1,d3_11_2,d3_9_2,d4_13_2]
  ring
#print axioms coefficient_13_2
compact_certificate_declaration theorem coefficient_13_3 (y z w b u : ℂ) :
    (innerCertificate13 y z w b u)[3]?=some 0 := by
  change some (((((((d0_8_3 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_9_3 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_10_2 y z w b u)*(d1_3_1 y z w b u))+(((d0_10_3 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_11_1 y z w b u)*(d1_2_2 y z w b u))+(((d0_11_2 y z w b u)*(d1_2_1 y z w b u))+(((d0_11_3 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_12_1 y z w b u)*(d1_1_2 y z w b u))+(((d0_12_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_12_3 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_13_1 y z w b u)*(d1_0_2 y z w b u))+(((d0_13_2 y z w b u)*(d1_0_1 y z w b u))+(((d0_13_3 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_11_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_11_2 y z w b u))+((d2_2_2 y z w b u)*(d3_11_1 y z w b u))))+((((d2_3_0 y z w b u)*(d3_10_3 y z w b u))+((d2_3_1 y z w b u)*(d3_10_2 y z w b u)))+((d2_4_0 y z w b u)*(d3_9_3 y z w b u)))))+((-1)*(d4_13_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_2,d0_10_3,d0_11_1,d0_11_2,d0_11_3,d0_12_1,d0_12_2,d0_12_3,d0_13_1,d0_13_2,d0_13_3,d0_8_3,d0_9_3,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_10_2,d3_10_3,d3_11_1,d3_11_2,d3_11_3,d3_9_3,d4_13_3]
  ring
#print axioms coefficient_13_3
compact_certificate_declaration theorem coefficient_13_4 (y z w b u : ℂ) :
    (innerCertificate13 y z w b u)[4]?=some 0 := by
  change some (((((((d0_8_4 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_9_4 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_10_3 y z w b u)*(d1_3_1 y z w b u))+(((d0_10_4 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_11_2 y z w b u)*(d1_2_2 y z w b u))+(((d0_11_3 y z w b u)*(d1_2_1 y z w b u))+(((d0_11_4 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_12_2 y z w b u)*(d1_1_2 y z w b u))+(((d0_12_3 y z w b u)*(d1_1_1 y z w b u))+(((d0_12_4 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_13_2 y z w b u)*(d1_0_2 y z w b u))+((d0_13_3 y z w b u)*(d1_0_1 y z w b u))))))))+((((d2_2_0 y z w b u)*(d3_11_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_11_3 y z w b u))+((d2_2_2 y z w b u)*(d3_11_2 y z w b u))))+((((d2_3_0 y z w b u)*(d3_10_4 y z w b u))+((d2_3_1 y z w b u)*(d3_10_3 y z w b u)))+((d2_4_0 y z w b u)*(d3_9_4 y z w b u)))))+((-1)*(d4_13_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_3,d0_10_4,d0_11_2,d0_11_3,d0_11_4,d0_12_2,d0_12_3,d0_12_4,d0_13_2,d0_13_3,d0_8_4,d0_9_4,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_10_3,d3_10_4,d3_11_2,d3_11_3,d3_11_4,d3_9_4,d4_13_4]
  ring
#print axioms coefficient_13_4

compact_certificate_declaration theorem coefficient_13_5 (y z w b u : ℂ) :
    (innerCertificate13 y z w b u)[5]?=some 0 := by
  change some (((((((d0_8_5 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_9_5 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_10_4 y z w b u)*(d1_3_1 y z w b u))+(((d0_10_5 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_11_3 y z w b u)*(d1_2_2 y z w b u))+((d0_11_4 y z w b u)*(d1_2_1 y z w b u)))+((((d0_12_3 y z w b u)*(d1_1_2 y z w b u))+((d0_12_4 y z w b u)*(d1_1_1 y z w b u)))+((d0_13_3 y z w b u)*(d1_0_2 y z w b u)))))))+((((d2_2_1 y z w b u)*(d3_11_4 y z w b u))+((d2_2_2 y z w b u)*(d3_11_3 y z w b u)))+((((d2_3_0 y z w b u)*(d3_10_5 y z w b u))+((d2_3_1 y z w b u)*(d3_10_4 y z w b u)))+((d2_4_0 y z w b u)*(d3_9_5 y z w b u)))))+((-1)*(d4_13_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_4,d0_10_5,d0_11_3,d0_11_4,d0_12_3,d0_12_4,d0_13_3,d0_8_5,d0_9_5,d1_0_2,d1_1_1,d1_1_2,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_10_4,d3_10_5,d3_11_3,d3_11_4,d3_9_5,d4_13_5]
  ring
#print axioms coefficient_13_5
compact_certificate_declaration theorem coefficient_13_6 (y z w b u : ℂ) :
    (innerCertificate13 y z w b u)[6]?=some 0 := by
  change some (((((((d0_8_6 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_9_6 y z w b u)*(d1_4_0 y z w b u))+0)+(((d0_10_5 y z w b u)*(d1_3_1 y z w b u))+(((d0_11_4 y z w b u)*(d1_2_2 y z w b u))+((d0_12_4 y z w b u)*(d1_1_2 y z w b u))))))+(((d2_2_2 y z w b u)*(d3_11_4 y z w b u))+(((d2_3_1 y z w b u)*(d3_10_5 y z w b u))+((d2_4_0 y z w b u)*(d3_9_6 y z w b u)))))+((-1)*(d4_13_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_5,d0_11_4,d0_12_4,d0_8_6,d0_9_6,d1_1_2,d1_2_2,d1_3_1,d1_4_0,d1_5_0,d2_2_2,d2_3_1,d2_4_0,d3_10_5,d3_11_4,d3_9_6,d4_13_6]
  ring
#print axioms coefficient_13_6

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_14 (y z w b u : ℂ) : (innerCertificate14 y z w b u).length=7 := by
  norm_num [innerCertificate14,add,multiply,scale,inner0_10,inner0_11,inner0_12,inner0_13,inner0_14,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner1_4,inner1_5,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner4_14]
compact_certificate_declaration theorem inner_eval_14 (y z w a b u : ℂ) :
    evaluate a (innerCertificate14 y z w b u)=(((((c0_9 y z w a b u)*(c1_5 y z w a b u))+(((c0_10 y z w a b u)*(c1_4 y z w a b u))+(((c0_11 y z w a b u)*(c1_3 y z w a b u))+(((c0_12 y z w a b u)*(c1_2 y z w a b u))+(((c0_13 y z w a b u)*(c1_1 y z w a b u))+(((c0_14 y z w a b u)*(c1_0 y z w a b u))+0))))))+(((c2_0 y z w a b u)*(c3_14 y z w a b u))+(((c2_1 y z w a b u)*(c3_13 y z w a b u))+(((c2_2 y z w a b u)*(c3_12 y z w a b u))+(((c2_3 y z w a b u)*(c3_11 y z w a b u))+((c2_4 y z w a b u)*(c3_10 y z w a b u)))))))+((-1)*(c4_14 y z w a b u))) := by
  simp only [innerCertificate14,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_10,c0_11,c0_12,c0_13,c0_14,c0_9,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_0,c2_1,c2_2,c2_3,c2_4,c3_10,c3_11,c3_12,c3_13,c3_14,c4_14]
#print axioms inner_eval_14

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_14_0 (y z w b u : ℂ) :
    (innerCertificate14 y z w b u)[0]?=some 0 := by
  change some (((((((d0_9_0 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_10_0 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_11_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_12_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_13_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_14_0 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_12_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_11_0 y z w b u))+0)+(((d2_4_0 y z w b u)*(d3_10_0 y z w b u))+0))))+(((-1)*(d4_14_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_11_0,d0_12_0,d0_13_0,d0_14_0,d0_9_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d1_4_0,d1_5_0,d2_2_0,d2_3_0,d2_4_0,d3_10_0,d3_11_0,d3_12_0,d4_14_0]
  ring
#print axioms coefficient_14_0
compact_certificate_declaration theorem coefficient_14_1 (y z w b u : ℂ) :
    (innerCertificate14 y z w b u)[1]?=some 0 := by
  change some (((((((d0_9_1 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_10_1 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_11_0 y z w b u)*(d1_3_1 y z w b u))+(((d0_11_1 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_12_0 y z w b u)*(d1_2_1 y z w b u))+(((d0_12_1 y z w b u)*(d1_2_0 y z w b u))+0))+((((d0_13_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_13_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_14_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_14_1 y z w b u)*(d1_0_0 y z w b u))+0)))))))+((((d2_2_0 y z w b u)*(d3_12_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_12_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_11_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_11_0 y z w b u))+0))+((d2_4_0 y z w b u)*(d3_10_1 y z w b u)))))+((-1)*(d4_14_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_1,d0_11_0,d0_11_1,d0_12_0,d0_12_1,d0_13_0,d0_13_1,d0_14_0,d0_14_1,d0_9_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_2_1,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d3_10_1,d3_11_0,d3_11_1,d3_12_0,d3_12_1,d4_14_1]
  ring
#print axioms coefficient_14_1

compact_certificate_declaration theorem coefficient_14_2 (y z w b u : ℂ) :
    (innerCertificate14 y z w b u)[2]?=some 0 := by
  change some (((((((d0_9_2 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_10_2 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_11_1 y z w b u)*(d1_3_1 y z w b u))+(((d0_11_2 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_12_0 y z w b u)*(d1_2_2 y z w b u))+(((d0_12_1 y z w b u)*(d1_2_1 y z w b u))+(((d0_12_2 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_13_0 y z w b u)*(d1_1_2 y z w b u))+(((d0_13_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_13_2 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_14_0 y z w b u)*(d1_0_2 y z w b u))+(((d0_14_1 y z w b u)*(d1_0_1 y z w b u))+(((d0_14_2 y z w b u)*(d1_0_0 y z w b u))+0))))))))+((((d2_2_0 y z w b u)*(d3_12_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_12_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_12_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_11_2 y z w b u))+((d2_3_1 y z w b u)*(d3_11_1 y z w b u)))+((d2_4_0 y z w b u)*(d3_10_2 y z w b u)))))+((-1)*(d4_14_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_2,d0_11_1,d0_11_2,d0_12_0,d0_12_1,d0_12_2,d0_13_0,d0_13_1,d0_13_2,d0_14_0,d0_14_1,d0_14_2,d0_9_2,d1_0_0,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_10_2,d3_11_1,d3_11_2,d3_12_0,d3_12_1,d3_12_2,d4_14_2]
  ring
#print axioms coefficient_14_2
compact_certificate_declaration theorem coefficient_14_3 (y z w b u : ℂ) :
    (innerCertificate14 y z w b u)[3]?=some 0 := by
  change some (((((((d0_9_3 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_10_3 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_11_2 y z w b u)*(d1_3_1 y z w b u))+(((d0_11_3 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_12_1 y z w b u)*(d1_2_2 y z w b u))+(((d0_12_2 y z w b u)*(d1_2_1 y z w b u))+(((d0_12_3 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_13_1 y z w b u)*(d1_1_2 y z w b u))+(((d0_13_2 y z w b u)*(d1_1_1 y z w b u))+(((d0_13_3 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_14_1 y z w b u)*(d1_0_2 y z w b u))+((d0_14_2 y z w b u)*(d1_0_1 y z w b u))))))))+((((d2_2_0 y z w b u)*(d3_12_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_12_2 y z w b u))+((d2_2_2 y z w b u)*(d3_12_1 y z w b u))))+((((d2_3_0 y z w b u)*(d3_11_3 y z w b u))+((d2_3_1 y z w b u)*(d3_11_2 y z w b u)))+((d2_4_0 y z w b u)*(d3_10_3 y z w b u)))))+((-1)*(d4_14_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_3,d0_11_2,d0_11_3,d0_12_1,d0_12_2,d0_12_3,d0_13_1,d0_13_2,d0_13_3,d0_14_1,d0_14_2,d0_9_3,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_10_3,d3_11_2,d3_11_3,d3_12_1,d3_12_2,d3_12_3,d4_14_3]
  ring
#print axioms coefficient_14_3
compact_certificate_declaration theorem coefficient_14_4 (y z w b u : ℂ) :
    (innerCertificate14 y z w b u)[4]?=some 0 := by
  change some (((((((d0_9_4 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_10_4 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_11_3 y z w b u)*(d1_3_1 y z w b u))+(((d0_11_4 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_12_2 y z w b u)*(d1_2_2 y z w b u))+(((d0_12_3 y z w b u)*(d1_2_1 y z w b u))+(((d0_12_4 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_13_2 y z w b u)*(d1_1_2 y z w b u))+((d0_13_3 y z w b u)*(d1_1_1 y z w b u)))+((d0_14_2 y z w b u)*(d1_0_2 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_12_4 y z w b u))+(((d2_2_1 y z w b u)*(d3_12_3 y z w b u))+((d2_2_2 y z w b u)*(d3_12_2 y z w b u))))+((((d2_3_0 y z w b u)*(d3_11_4 y z w b u))+((d2_3_1 y z w b u)*(d3_11_3 y z w b u)))+((d2_4_0 y z w b u)*(d3_10_4 y z w b u)))))+((-1)*(d4_14_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_4,d0_11_3,d0_11_4,d0_12_2,d0_12_3,d0_12_4,d0_13_2,d0_13_3,d0_14_2,d0_9_4,d1_0_2,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_10_4,d3_11_3,d3_11_4,d3_12_2,d3_12_3,d3_12_4,d4_14_4]
  ring
#print axioms coefficient_14_4

compact_certificate_declaration theorem coefficient_14_5 (y z w b u : ℂ) :
    (innerCertificate14 y z w b u)[5]?=some 0 := by
  change some (((((((d0_9_5 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_10_5 y z w b u)*(d1_4_0 y z w b u))+0)+(((d0_11_4 y z w b u)*(d1_3_1 y z w b u))+((((d0_12_3 y z w b u)*(d1_2_2 y z w b u))+((d0_12_4 y z w b u)*(d1_2_1 y z w b u)))+((d0_13_3 y z w b u)*(d1_1_2 y z w b u))))))+((((d2_2_1 y z w b u)*(d3_12_4 y z w b u))+((d2_2_2 y z w b u)*(d3_12_3 y z w b u)))+(((d2_3_1 y z w b u)*(d3_11_4 y z w b u))+((d2_4_0 y z w b u)*(d3_10_5 y z w b u)))))+((-1)*(d4_14_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_5,d0_11_4,d0_12_3,d0_12_4,d0_13_3,d0_9_5,d1_1_2,d1_2_1,d1_2_2,d1_3_1,d1_4_0,d1_5_0,d2_2_1,d2_2_2,d2_3_1,d2_4_0,d3_10_5,d3_11_4,d3_12_3,d3_12_4,d4_14_5]
  ring
#print axioms coefficient_14_5
compact_certificate_declaration theorem coefficient_14_6 (y z w b u : ℂ) :
    (innerCertificate14 y z w b u)[6]?=some 0 := by
  change some (((((((d0_9_6 y z w b u)*(d1_5_0 y z w b u))+0)+((d0_12_4 y z w b u)*(d1_2_2 y z w b u)))+((d2_2_2 y z w b u)*(d3_12_4 y z w b u)))+((-1)*(d4_14_6 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_12_4,d0_9_6,d1_2_2,d1_5_0,d2_2_2,d3_12_4,d4_14_6]
  ring
#print axioms coefficient_14_6

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_15 (y z w b u : ℂ) : (innerCertificate15 y z w b u).length=6 := by
  norm_num [innerCertificate15,add,multiply,scale,inner0_10,inner0_11,inner0_12,inner0_13,inner0_14,inner0_15,inner1_0,inner1_1,inner1_2,inner1_3,inner1_4,inner1_5,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner4_15]
compact_certificate_declaration theorem inner_eval_15 (y z w a b u : ℂ) :
    evaluate a (innerCertificate15 y z w b u)=(((((c0_10 y z w a b u)*(c1_5 y z w a b u))+(((c0_11 y z w a b u)*(c1_4 y z w a b u))+(((c0_12 y z w a b u)*(c1_3 y z w a b u))+(((c0_13 y z w a b u)*(c1_2 y z w a b u))+(((c0_14 y z w a b u)*(c1_1 y z w a b u))+(((c0_15 y z w a b u)*(c1_0 y z w a b u))+0))))))+(((c2_0 y z w a b u)*(c3_15 y z w a b u))+(((c2_1 y z w a b u)*(c3_14 y z w a b u))+(((c2_2 y z w a b u)*(c3_13 y z w a b u))+(((c2_3 y z w a b u)*(c3_12 y z w a b u))+((c2_4 y z w a b u)*(c3_11 y z w a b u)))))))+((-1)*(c4_15 y z w a b u))) := by
  simp only [innerCertificate15,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_10,c0_11,c0_12,c0_13,c0_14,c0_15,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_0,c2_1,c2_2,c2_3,c2_4,c3_11,c3_12,c3_13,c3_14,c3_15,c4_15]
#print axioms inner_eval_15

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_15_0 (y z w b u : ℂ) :
    (innerCertificate15 y z w b u)[0]?=some 0 := by
  change some (((((((d0_10_0 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_11_0 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_12_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_13_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_14_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_15_0 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_13_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_12_0 y z w b u))+0)+(((d2_4_0 y z w b u)*(d3_11_0 y z w b u))+0))))+(((-1)*(d4_15_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_0,d0_11_0,d0_12_0,d0_13_0,d0_14_0,d0_15_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d1_4_0,d1_5_0,d2_2_0,d2_3_0,d2_4_0,d3_11_0,d3_12_0,d3_13_0,d4_15_0]
  ring
#print axioms coefficient_15_0
compact_certificate_declaration theorem coefficient_15_1 (y z w b u : ℂ) :
    (innerCertificate15 y z w b u)[1]?=some 0 := by
  change some (((((((d0_10_1 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_11_1 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_12_0 y z w b u)*(d1_3_1 y z w b u))+(((d0_12_1 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_13_0 y z w b u)*(d1_2_1 y z w b u))+(((d0_13_1 y z w b u)*(d1_2_0 y z w b u))+0))+((((d0_14_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_14_1 y z w b u)*(d1_1_0 y z w b u))+0))+(((d0_15_0 y z w b u)*(d1_0_1 y z w b u))+(((d0_15_1 y z w b u)*(d1_0_0 y z w b u))+0)))))))+((((d2_2_0 y z w b u)*(d3_13_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_13_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_12_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_12_0 y z w b u))+0))+((d2_4_0 y z w b u)*(d3_11_1 y z w b u)))))+((-1)*(d4_15_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_1,d0_11_1,d0_12_0,d0_12_1,d0_13_0,d0_13_1,d0_14_0,d0_14_1,d0_15_0,d0_15_1,d1_0_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_2_1,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d3_11_1,d3_12_0,d3_12_1,d3_13_0,d3_13_1,d4_15_1]
  ring
#print axioms coefficient_15_1
compact_certificate_declaration theorem coefficient_15_2 (y z w b u : ℂ) :
    (innerCertificate15 y z w b u)[2]?=some 0 := by
  change some (((((((d0_10_2 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_11_2 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_12_1 y z w b u)*(d1_3_1 y z w b u))+(((d0_12_2 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_13_0 y z w b u)*(d1_2_2 y z w b u))+(((d0_13_1 y z w b u)*(d1_2_1 y z w b u))+(((d0_13_2 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_14_0 y z w b u)*(d1_1_2 y z w b u))+(((d0_14_1 y z w b u)*(d1_1_1 y z w b u))+(((d0_14_2 y z w b u)*(d1_1_0 y z w b u))+0)))+(((d0_15_0 y z w b u)*(d1_0_2 y z w b u))+((d0_15_1 y z w b u)*(d1_0_1 y z w b u))))))))+((((d2_2_0 y z w b u)*(d3_13_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_13_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_13_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_12_2 y z w b u))+((d2_3_1 y z w b u)*(d3_12_1 y z w b u)))+((d2_4_0 y z w b u)*(d3_11_2 y z w b u)))))+((-1)*(d4_15_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_2,d0_11_2,d0_12_1,d0_12_2,d0_13_0,d0_13_1,d0_13_2,d0_14_0,d0_14_1,d0_14_2,d0_15_0,d0_15_1,d1_0_1,d1_0_2,d1_1_0,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_11_2,d3_12_1,d3_12_2,d3_13_0,d3_13_1,d3_13_2,d4_15_2]
  ring
#print axioms coefficient_15_2

compact_certificate_declaration theorem coefficient_15_3 (y z w b u : ℂ) :
    (innerCertificate15 y z w b u)[3]?=some 0 := by
  change some (((((((d0_10_3 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_11_3 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_12_2 y z w b u)*(d1_3_1 y z w b u))+(((d0_12_3 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_13_1 y z w b u)*(d1_2_2 y z w b u))+(((d0_13_2 y z w b u)*(d1_2_1 y z w b u))+(((d0_13_3 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_14_1 y z w b u)*(d1_1_2 y z w b u))+((d0_14_2 y z w b u)*(d1_1_1 y z w b u)))+((d0_15_1 y z w b u)*(d1_0_2 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_13_3 y z w b u))+(((d2_2_1 y z w b u)*(d3_13_2 y z w b u))+((d2_2_2 y z w b u)*(d3_13_1 y z w b u))))+((((d2_3_0 y z w b u)*(d3_12_3 y z w b u))+((d2_3_1 y z w b u)*(d3_12_2 y z w b u)))+((d2_4_0 y z w b u)*(d3_11_3 y z w b u)))))+((-1)*(d4_15_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_3,d0_11_3,d0_12_2,d0_12_3,d0_13_1,d0_13_2,d0_13_3,d0_14_1,d0_14_2,d0_15_1,d1_0_2,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_11_3,d3_12_2,d3_12_3,d3_13_1,d3_13_2,d3_13_3,d4_15_3]
  ring
#print axioms coefficient_15_3
compact_certificate_declaration theorem coefficient_15_4 (y z w b u : ℂ) :
    (innerCertificate15 y z w b u)[4]?=some 0 := by
  change some (((((((d0_10_4 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_11_4 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_12_3 y z w b u)*(d1_3_1 y z w b u))+(((d0_12_4 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_13_2 y z w b u)*(d1_2_2 y z w b u))+((d0_13_3 y z w b u)*(d1_2_1 y z w b u)))+((d0_14_2 y z w b u)*(d1_1_2 y z w b u))))))+((((d2_2_1 y z w b u)*(d3_13_3 y z w b u))+((d2_2_2 y z w b u)*(d3_13_2 y z w b u)))+((((d2_3_0 y z w b u)*(d3_12_4 y z w b u))+((d2_3_1 y z w b u)*(d3_12_3 y z w b u)))+((d2_4_0 y z w b u)*(d3_11_4 y z w b u)))))+((-1)*(d4_15_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_4,d0_11_4,d0_12_3,d0_12_4,d0_13_2,d0_13_3,d0_14_2,d1_1_2,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_11_4,d3_12_3,d3_12_4,d3_13_2,d3_13_3,d4_15_4]
  ring
#print axioms coefficient_15_4
compact_certificate_declaration theorem coefficient_15_5 (y z w b u : ℂ) :
    (innerCertificate15 y z w b u)[5]?=some 0 := by
  change some (((((((d0_10_5 y z w b u)*(d1_5_0 y z w b u))+0)+(((d0_12_4 y z w b u)*(d1_3_1 y z w b u))+((d0_13_3 y z w b u)*(d1_2_2 y z w b u))))+(((d2_2_2 y z w b u)*(d3_13_3 y z w b u))+((d2_3_1 y z w b u)*(d3_12_4 y z w b u))))+((-1)*(d4_15_5 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_10_5,d0_12_4,d0_13_3,d1_2_2,d1_3_1,d1_5_0,d2_2_2,d2_3_1,d3_12_4,d3_13_3,d4_15_5]
  ring
#print axioms coefficient_15_5

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_16 (y z w b u : ℂ) : (innerCertificate16 y z w b u).length=5 := by
  norm_num [innerCertificate16,add,multiply,scale,inner0_11,inner0_12,inner0_13,inner0_14,inner0_15,inner0_16,inner1_0,inner1_1,inner1_2,inner1_3,inner1_4,inner1_5,inner2_1,inner2_2,inner2_3,inner2_4,inner3_12,inner3_13,inner3_14,inner3_15,inner4_16]
compact_certificate_declaration theorem inner_eval_16 (y z w a b u : ℂ) :
    evaluate a (innerCertificate16 y z w b u)=(((((c0_11 y z w a b u)*(c1_5 y z w a b u))+(((c0_12 y z w a b u)*(c1_4 y z w a b u))+(((c0_13 y z w a b u)*(c1_3 y z w a b u))+(((c0_14 y z w a b u)*(c1_2 y z w a b u))+(((c0_15 y z w a b u)*(c1_1 y z w a b u))+(((c0_16 y z w a b u)*(c1_0 y z w a b u))+0))))))+(((c2_1 y z w a b u)*(c3_15 y z w a b u))+(((c2_2 y z w a b u)*(c3_14 y z w a b u))+(((c2_3 y z w a b u)*(c3_13 y z w a b u))+((c2_4 y z w a b u)*(c3_12 y z w a b u))))))+((-1)*(c4_16 y z w a b u))) := by
  simp only [innerCertificate16,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_11,c0_12,c0_13,c0_14,c0_15,c0_16,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_1,c2_2,c2_3,c2_4,c3_12,c3_13,c3_14,c3_15,c4_16]
#print axioms inner_eval_16

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_16_0 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[0]?=some 0 := by
  change some (((((((d0_11_0 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_12_0 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_13_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_14_0 y z w b u)*(d1_2_0 y z w b u))+0)+((((d0_15_0 y z w b u)*(d1_1_0 y z w b u))+0)+(((d0_16_0 y z w b u)*(d1_0_0 y z w b u))+0))))))+((((d2_2_0 y z w b u)*(d3_14_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_13_0 y z w b u))+0)+(((d2_4_0 y z w b u)*(d3_12_0 y z w b u))+0))))+(((-1)*(d4_16_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_11_0,d0_12_0,d0_13_0,d0_14_0,d0_15_0,d0_16_0,d1_0_0,d1_1_0,d1_2_0,d1_3_0,d1_4_0,d1_5_0,d2_2_0,d2_3_0,d2_4_0,d3_12_0,d3_13_0,d3_14_0,d4_16_0]
  ring
#print axioms coefficient_16_0
compact_certificate_declaration theorem coefficient_16_1 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[1]?=some 0 := by
  change some (((((((d0_11_1 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_12_1 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_13_0 y z w b u)*(d1_3_1 y z w b u))+(((d0_13_1 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_14_0 y z w b u)*(d1_2_1 y z w b u))+(((d0_14_1 y z w b u)*(d1_2_0 y z w b u))+0))+((((d0_15_0 y z w b u)*(d1_1_1 y z w b u))+(((d0_15_1 y z w b u)*(d1_1_0 y z w b u))+0))+((d0_16_0 y z w b u)*(d1_0_1 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_14_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_14_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_13_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_13_0 y z w b u))+0))+((d2_4_0 y z w b u)*(d3_12_1 y z w b u)))))+((-1)*(d4_16_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_11_1,d0_12_1,d0_13_0,d0_13_1,d0_14_0,d0_14_1,d0_15_0,d0_15_1,d0_16_0,d1_0_1,d1_1_0,d1_1_1,d1_2_0,d1_2_1,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d3_12_1,d3_13_0,d3_13_1,d3_14_0,d3_14_1,d4_16_1]
  ring
#print axioms coefficient_16_1
compact_certificate_declaration theorem coefficient_16_2 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[2]?=some 0 := by
  change some (((((((d0_11_2 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_12_2 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_13_1 y z w b u)*(d1_3_1 y z w b u))+(((d0_13_2 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_14_0 y z w b u)*(d1_2_2 y z w b u))+(((d0_14_1 y z w b u)*(d1_2_1 y z w b u))+(((d0_14_2 y z w b u)*(d1_2_0 y z w b u))+0)))+((((d0_15_0 y z w b u)*(d1_1_2 y z w b u))+((d0_15_1 y z w b u)*(d1_1_1 y z w b u)))+((d0_16_0 y z w b u)*(d1_0_2 y z w b u)))))))+((((d2_2_0 y z w b u)*(d3_14_2 y z w b u))+(((d2_2_1 y z w b u)*(d3_14_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_14_0 y z w b u))+0)))+((((d2_3_0 y z w b u)*(d3_13_2 y z w b u))+((d2_3_1 y z w b u)*(d3_13_1 y z w b u)))+((d2_4_0 y z w b u)*(d3_12_2 y z w b u)))))+((-1)*(d4_16_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_11_2,d0_12_2,d0_13_1,d0_13_2,d0_14_0,d0_14_1,d0_14_2,d0_15_0,d0_15_1,d0_16_0,d1_0_2,d1_1_1,d1_1_2,d1_2_0,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_12_2,d3_13_1,d3_13_2,d3_14_0,d3_14_1,d3_14_2,d4_16_2]
  ring
#print axioms coefficient_16_2

compact_certificate_declaration theorem coefficient_16_3 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[3]?=some 0 := by
  change some (((((((d0_11_3 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_12_3 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_13_2 y z w b u)*(d1_3_1 y z w b u))+(((d0_13_3 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_14_1 y z w b u)*(d1_2_2 y z w b u))+((d0_14_2 y z w b u)*(d1_2_1 y z w b u)))+((d0_15_1 y z w b u)*(d1_1_2 y z w b u))))))+((((d2_2_1 y z w b u)*(d3_14_2 y z w b u))+((d2_2_2 y z w b u)*(d3_14_1 y z w b u)))+((((d2_3_0 y z w b u)*(d3_13_3 y z w b u))+((d2_3_1 y z w b u)*(d3_13_2 y z w b u)))+((d2_4_0 y z w b u)*(d3_12_3 y z w b u)))))+((-1)*(d4_16_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_11_3,d0_12_3,d0_13_2,d0_13_3,d0_14_1,d0_14_2,d0_15_1,d1_1_2,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_12_3,d3_13_2,d3_13_3,d3_14_1,d3_14_2,d4_16_3]
  ring
#print axioms coefficient_16_3
compact_certificate_declaration theorem coefficient_16_4 (y z w b u : ℂ) :
    (innerCertificate16 y z w b u)[4]?=some 0 := by
  change some (((((((d0_11_4 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_12_4 y z w b u)*(d1_4_0 y z w b u))+0)+(((d0_13_3 y z w b u)*(d1_3_1 y z w b u))+((d0_14_2 y z w b u)*(d1_2_2 y z w b u)))))+(((d2_2_2 y z w b u)*(d3_14_2 y z w b u))+(((d2_3_1 y z w b u)*(d3_13_3 y z w b u))+((d2_4_0 y z w b u)*(d3_12_4 y z w b u)))))+((-1)*(d4_16_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_11_4,d0_12_4,d0_13_3,d0_14_2,d1_2_2,d1_3_1,d1_4_0,d1_5_0,d2_2_2,d2_3_1,d2_4_0,d3_12_4,d3_13_3,d3_14_2,d4_16_4]
  ring
#print axioms coefficient_16_4

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_17 (y z w b u : ℂ) : (innerCertificate17 y z w b u).length=5 := by
  norm_num [innerCertificate17,add,multiply,scale,inner0_12,inner0_13,inner0_14,inner0_15,inner0_16,inner1_1,inner1_2,inner1_3,inner1_4,inner1_5,inner2_2,inner2_3,inner2_4,inner3_13,inner3_14,inner3_15,inner4_17]
compact_certificate_declaration theorem inner_eval_17 (y z w a b u : ℂ) :
    evaluate a (innerCertificate17 y z w b u)=(((((c0_12 y z w a b u)*(c1_5 y z w a b u))+(((c0_13 y z w a b u)*(c1_4 y z w a b u))+(((c0_14 y z w a b u)*(c1_3 y z w a b u))+(((c0_15 y z w a b u)*(c1_2 y z w a b u))+((c0_16 y z w a b u)*(c1_1 y z w a b u))))))+(((c2_2 y z w a b u)*(c3_15 y z w a b u))+(((c2_3 y z w a b u)*(c3_14 y z w a b u))+((c2_4 y z w a b u)*(c3_13 y z w a b u)))))+((-1)*(c4_17 y z w a b u))) := by
  simp only [innerCertificate17,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_12,c0_13,c0_14,c0_15,c0_16,c1_1,c1_2,c1_3,c1_4,c1_5,c2_2,c2_3,c2_4,c3_13,c3_14,c3_15,c4_17]
#print axioms inner_eval_17

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_17_0 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[0]?=some 0 := by
  change some (((((((d0_12_0 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_13_0 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_14_0 y z w b u)*(d1_3_0 y z w b u))+0)+((((d0_15_0 y z w b u)*(d1_2_0 y z w b u))+0)+(((d0_16_0 y z w b u)*(d1_1_0 y z w b u))+0)))))+((((d2_2_0 y z w b u)*(d3_15_0 y z w b u))+0)+((((d2_3_0 y z w b u)*(d3_14_0 y z w b u))+0)+(((d2_4_0 y z w b u)*(d3_13_0 y z w b u))+0))))+(((-1)*(d4_17_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_12_0,d0_13_0,d0_14_0,d0_15_0,d0_16_0,d1_1_0,d1_2_0,d1_3_0,d1_4_0,d1_5_0,d2_2_0,d2_3_0,d2_4_0,d3_13_0,d3_14_0,d3_15_0,d4_17_0]
  ring
#print axioms coefficient_17_0
compact_certificate_declaration theorem coefficient_17_1 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[1]?=some 0 := by
  change some (((((((d0_12_1 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_13_1 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_14_0 y z w b u)*(d1_3_1 y z w b u))+(((d0_14_1 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_15_0 y z w b u)*(d1_2_1 y z w b u))+(((d0_15_1 y z w b u)*(d1_2_0 y z w b u))+0))+((d0_16_0 y z w b u)*(d1_1_1 y z w b u))))))+((((d2_2_0 y z w b u)*(d3_15_1 y z w b u))+(((d2_2_1 y z w b u)*(d3_15_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_14_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_14_0 y z w b u))+0))+((d2_4_0 y z w b u)*(d3_13_1 y z w b u)))))+((-1)*(d4_17_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_12_1,d0_13_1,d0_14_0,d0_14_1,d0_15_0,d0_15_1,d0_16_0,d1_1_1,d1_2_0,d1_2_1,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_0,d2_2_1,d2_3_0,d2_3_1,d2_4_0,d3_13_1,d3_14_0,d3_14_1,d3_15_0,d3_15_1,d4_17_1]
  ring
#print axioms coefficient_17_1
compact_certificate_declaration theorem coefficient_17_2 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[2]?=some 0 := by
  change some (((((((d0_12_2 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_13_2 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_14_1 y z w b u)*(d1_3_1 y z w b u))+(((d0_14_2 y z w b u)*(d1_3_0 y z w b u))+0))+((((d0_15_0 y z w b u)*(d1_2_2 y z w b u))+((d0_15_1 y z w b u)*(d1_2_1 y z w b u)))+((d0_16_0 y z w b u)*(d1_1_2 y z w b u))))))+((((d2_2_1 y z w b u)*(d3_15_1 y z w b u))+(((d2_2_2 y z w b u)*(d3_15_0 y z w b u))+0))+((((d2_3_0 y z w b u)*(d3_14_2 y z w b u))+((d2_3_1 y z w b u)*(d3_14_1 y z w b u)))+((d2_4_0 y z w b u)*(d3_13_2 y z w b u)))))+((-1)*(d4_17_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_12_2,d0_13_2,d0_14_1,d0_14_2,d0_15_0,d0_15_1,d0_16_0,d1_1_2,d1_2_1,d1_2_2,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_2_1,d2_2_2,d2_3_0,d2_3_1,d2_4_0,d3_13_2,d3_14_1,d3_14_2,d3_15_0,d3_15_1,d4_17_2]
  ring
#print axioms coefficient_17_2

compact_certificate_declaration theorem coefficient_17_3 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[3]?=some 0 := by
  change some (((((((d0_12_3 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_13_3 y z w b u)*(d1_4_0 y z w b u))+0)+(((d0_14_2 y z w b u)*(d1_3_1 y z w b u))+((d0_15_1 y z w b u)*(d1_2_2 y z w b u)))))+(((d2_2_2 y z w b u)*(d3_15_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_14_2 y z w b u))+((d2_4_0 y z w b u)*(d3_13_3 y z w b u)))))+((-1)*(d4_17_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_12_3,d0_13_3,d0_14_2,d0_15_1,d1_2_2,d1_3_1,d1_4_0,d1_5_0,d2_2_2,d2_3_1,d2_4_0,d3_13_3,d3_14_2,d3_15_1,d4_17_3]
  ring
#print axioms coefficient_17_3
compact_certificate_declaration theorem coefficient_17_4 (y z w b u : ℂ) :
    (innerCertificate17 y z w b u)[4]?=some 0 := by
  change some (((((d0_12_4 y z w b u)*(d1_5_0 y z w b u))+0)+((-1)*(d4_17_4 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_12_4,d1_5_0,d4_17_4]
  ring
#print axioms coefficient_17_4

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_18 (y z w b u : ℂ) : (innerCertificate18 y z w b u).length=4 := by
  norm_num [innerCertificate18,add,multiply,scale,inner0_13,inner0_14,inner0_15,inner0_16,inner1_2,inner1_3,inner1_4,inner1_5,inner2_3,inner2_4,inner3_14,inner3_15,inner4_18]
compact_certificate_declaration theorem inner_eval_18 (y z w a b u : ℂ) :
    evaluate a (innerCertificate18 y z w b u)=(((((c0_13 y z w a b u)*(c1_5 y z w a b u))+(((c0_14 y z w a b u)*(c1_4 y z w a b u))+(((c0_15 y z w a b u)*(c1_3 y z w a b u))+((c0_16 y z w a b u)*(c1_2 y z w a b u)))))+(((c2_3 y z w a b u)*(c3_15 y z w a b u))+((c2_4 y z w a b u)*(c3_14 y z w a b u))))+((-1)*(c4_18 y z w a b u))) := by
  simp only [innerCertificate18,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_13,c0_14,c0_15,c0_16,c1_2,c1_3,c1_4,c1_5,c2_3,c2_4,c3_14,c3_15,c4_18]
#print axioms inner_eval_18

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem coefficient_18_0 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[0]?=some 0 := by
  change some (((((((d0_13_0 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_14_0 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_15_0 y z w b u)*(d1_3_0 y z w b u))+0)+(((d0_16_0 y z w b u)*(d1_2_0 y z w b u))+0))))+((((d2_3_0 y z w b u)*(d3_15_0 y z w b u))+0)+(((d2_4_0 y z w b u)*(d3_14_0 y z w b u))+0)))+(((-1)*(d4_18_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_0,d0_14_0,d0_15_0,d0_16_0,d1_2_0,d1_3_0,d1_4_0,d1_5_0,d2_3_0,d2_4_0,d3_14_0,d3_15_0,d4_18_0]
  ring
#print axioms coefficient_18_0
compact_certificate_declaration theorem coefficient_18_1 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[1]?=some 0 := by
  change some (((((((d0_13_1 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_14_1 y z w b u)*(d1_4_0 y z w b u))+0)+((((d0_15_0 y z w b u)*(d1_3_1 y z w b u))+(((d0_15_1 y z w b u)*(d1_3_0 y z w b u))+0))+((d0_16_0 y z w b u)*(d1_2_1 y z w b u)))))+((((d2_3_0 y z w b u)*(d3_15_1 y z w b u))+(((d2_3_1 y z w b u)*(d3_15_0 y z w b u))+0))+((d2_4_0 y z w b u)*(d3_14_1 y z w b u))))+((-1)*(d4_18_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_1,d0_14_1,d0_15_0,d0_15_1,d0_16_0,d1_2_1,d1_3_0,d1_3_1,d1_4_0,d1_5_0,d2_3_0,d2_3_1,d2_4_0,d3_14_1,d3_15_0,d3_15_1,d4_18_1]
  ring
#print axioms coefficient_18_1
compact_certificate_declaration theorem coefficient_18_2 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[2]?=some 0 := by
  change some (((((((d0_13_2 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_14_2 y z w b u)*(d1_4_0 y z w b u))+0)+(((d0_15_1 y z w b u)*(d1_3_1 y z w b u))+((d0_16_0 y z w b u)*(d1_2_2 y z w b u)))))+(((d2_3_1 y z w b u)*(d3_15_1 y z w b u))+((d2_4_0 y z w b u)*(d3_14_2 y z w b u))))+((-1)*(d4_18_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_2,d0_14_2,d0_15_1,d0_16_0,d1_2_2,d1_3_1,d1_4_0,d1_5_0,d2_3_1,d2_4_0,d3_14_2,d3_15_1,d4_18_2]
  ring
#print axioms coefficient_18_2

compact_certificate_declaration theorem coefficient_18_3 (y z w b u : ℂ) :
    (innerCertificate18 y z w b u)[3]?=some 0 := by
  change some (((((d0_13_3 y z w b u)*(d1_5_0 y z w b u))+0)+((-1)*(d4_18_3 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_13_3,d1_5_0,d4_18_3]
  ring
#print axioms coefficient_18_3

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_19 (y z w b u : ℂ) : (innerCertificate19 y z w b u).length=3 := by
  norm_num [innerCertificate19,add,multiply,scale,inner0_14,inner0_15,inner0_16,inner1_3,inner1_4,inner1_5,inner2_4,inner3_15,inner4_19]
compact_certificate_declaration theorem inner_eval_19 (y z w a b u : ℂ) :
    evaluate a (innerCertificate19 y z w b u)=(((((c0_14 y z w a b u)*(c1_5 y z w a b u))+(((c0_15 y z w a b u)*(c1_4 y z w a b u))+((c0_16 y z w a b u)*(c1_3 y z w a b u))))+((c2_4 y z w a b u)*(c3_15 y z w a b u)))+((-1)*(c4_19 y z w a b u))) := by
  simp only [innerCertificate19,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_14,c0_15,c0_16,c1_3,c1_4,c1_5,c2_4,c3_15,c4_19]
#print axioms inner_eval_19

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem coefficient_19_0 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[0]?=some 0 := by
  change some (((((((d0_14_0 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_15_0 y z w b u)*(d1_4_0 y z w b u))+0)+(((d0_16_0 y z w b u)*(d1_3_0 y z w b u))+0)))+(((d2_4_0 y z w b u)*(d3_15_0 y z w b u))+0))+(((-1)*(d4_19_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_0,d0_15_0,d0_16_0,d1_3_0,d1_4_0,d1_5_0,d2_4_0,d3_15_0,d4_19_0]
  ring
#print axioms coefficient_19_0
compact_certificate_declaration theorem coefficient_19_1 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[1]?=some 0 := by
  change some (((((((d0_14_1 y z w b u)*(d1_5_0 y z w b u))+0)+((((d0_15_1 y z w b u)*(d1_4_0 y z w b u))+0)+((d0_16_0 y z w b u)*(d1_3_1 y z w b u))))+((d2_4_0 y z w b u)*(d3_15_1 y z w b u)))+((-1)*(d4_19_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_1,d0_15_1,d0_16_0,d1_3_1,d1_4_0,d1_5_0,d2_4_0,d3_15_1,d4_19_1]
  ring
#print axioms coefficient_19_1
compact_certificate_declaration theorem coefficient_19_2 (y z w b u : ℂ) :
    (innerCertificate19 y z w b u)[2]?=some 0 := by
  change some (((((d0_14_2 y z w b u)*(d1_5_0 y z w b u))+0)+((-1)*(d4_19_2 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_14_2,d1_5_0,d4_19_2]
  ring
#print axioms coefficient_19_2

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_20 (y z w b u : ℂ) : (innerCertificate20 y z w b u).length=2 := by
  norm_num [innerCertificate20,add,multiply,scale,inner0_15,inner0_16,inner1_4,inner1_5,inner4_20]
compact_certificate_declaration theorem inner_eval_20 (y z w a b u : ℂ) :
    evaluate a (innerCertificate20 y z w b u)=((((c0_15 y z w a b u)*(c1_5 y z w a b u))+((c0_16 y z w a b u)*(c1_4 y z w a b u)))+((-1)*(c4_20 y z w a b u))) := by
  simp only [innerCertificate20,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_15,c0_16,c1_4,c1_5,c4_20]
#print axioms inner_eval_20

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem coefficient_20_0 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[0]?=some 0 := by
  change some ((((((d0_15_0 y z w b u)*(d1_5_0 y z w b u))+0)+(((d0_16_0 y z w b u)*(d1_4_0 y z w b u))+0))+(((-1)*(d4_20_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_0,d0_16_0,d1_4_0,d1_5_0,d4_20_0]
  ring
#print axioms coefficient_20_0
compact_certificate_declaration theorem coefficient_20_1 (y z w b u : ℂ) :
    (innerCertificate20 y z w b u)[1]?=some 0 := by
  change some (((((d0_15_1 y z w b u)*(d1_5_0 y z w b u))+0)+((-1)*(d4_20_1 y z w b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_15_1,d1_5_0,d4_20_1]
  ring
#print axioms coefficient_20_1

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem inner_length_21 (y z w b u : ℂ) : (innerCertificate21 y z w b u).length=1 := by
  norm_num [innerCertificate21,add,multiply,scale,inner0_16,inner1_5,inner4_21]
compact_certificate_declaration theorem inner_eval_21 (y z w a b u : ℂ) :
    evaluate a (innerCertificate21 y z w b u)=(((c0_16 y z w a b u)*(c1_5 y z w a b u))+((-1)*(c4_21 y z w a b u))) := by
  simp only [innerCertificate21,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_16,c1_5,c4_21]
#print axioms inner_eval_21

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem coefficient_21_0 (y z w b u : ℂ) :
    (innerCertificate21 y z w b u)[0]?=some 0 := by
  change some (((((d0_16_0 y z w b u)*(d1_5_0 y z w b u))+0)+(((-1)*(d4_21_0 y z w b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_16_0,d1_5_0,d4_21_0]
  ring
#print axioms coefficient_21_0

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem inner_zero_0 (y z w b u : ℂ) : ∀ v∈innerCertificate0 y z w b u,v=0 := by
  apply zero_of_getElem? _ 1 (inner_length_0 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_0_0 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 0 through 0 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_1 (y z w b u : ℂ) : ∀ v∈innerCertificate1 y z w b u,v=0 := by
  apply zero_of_getElem? _ 1 (inner_length_1 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_1_0 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 1 through 1 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_2 (y z w b u : ℂ) : ∀ v∈innerCertificate2 y z w b u,v=0 := by
  apply zero_of_getElem? _ 9 (inner_length_2 y z w b u)
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
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 2 through 2 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_3 (y z w b u : ℂ) : ∀ v∈innerCertificate3 y z w b u,v=0 := by
  apply zero_of_getElem? _ 10 (inner_length_3 y z w b u)
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
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 3 through 3 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_4 (y z w b u : ℂ) : ∀ v∈innerCertificate4 y z w b u,v=0 := by
  apply zero_of_getElem? _ 10 (inner_length_4 y z w b u)
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
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 4 through 4 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_5 (y z w b u : ℂ) : ∀ v∈innerCertificate5 y z w b u,v=0 := by
  apply zero_of_getElem? _ 10 (inner_length_5 y z w b u)
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
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 5 through 5 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_6 (y z w b u : ℂ) : ∀ v∈innerCertificate6 y z w b u,v=0 := by
  apply zero_of_getElem? _ 10 (inner_length_6 y z w b u)
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
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 6 through 6 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_7 (y z w b u : ℂ) : ∀ v∈innerCertificate7 y z w b u,v=0 := by
  apply zero_of_getElem? _ 10 (inner_length_7 y z w b u)
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
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 7 through 7 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_8 (y z w b u : ℂ) : ∀ v∈innerCertificate8 y z w b u,v=0 := by
  apply zero_of_getElem? _ 10 (inner_length_8 y z w b u)
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
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 8 through 8 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_9 (y z w b u : ℂ) : ∀ v∈innerCertificate9 y z w b u,v=0 := by
  apply zero_of_getElem? _ 10 (inner_length_9 y z w b u)
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
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 9 through 9 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_10 (y z w b u : ℂ) : ∀ v∈innerCertificate10 y z w b u,v=0 := by
  apply zero_of_getElem? _ 9 (inner_length_10 y z w b u)
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
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 10 through 10 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_11 (y z w b u : ℂ) : ∀ v∈innerCertificate11 y z w b u,v=0 := by
  apply zero_of_getElem? _ 9 (inner_length_11 y z w b u)
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
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 11 through 11 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_12 (y z w b u : ℂ) : ∀ v∈innerCertificate12 y z w b u,v=0 := by
  apply zero_of_getElem? _ 8 (inner_length_12 y z w b u)
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
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 12 through 12 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_13 (y z w b u : ℂ) : ∀ v∈innerCertificate13 y z w b u,v=0 := by
  apply zero_of_getElem? _ 7 (inner_length_13 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_13_0 y z w b u
  · exact coefficient_13_1 y z w b u
  · exact coefficient_13_2 y z w b u
  · exact coefficient_13_3 y z w b u
  · exact coefficient_13_4 y z w b u
  · exact coefficient_13_5 y z w b u
  · exact coefficient_13_6 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 13 through 13 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_14 (y z w b u : ℂ) : ∀ v∈innerCertificate14 y z w b u,v=0 := by
  apply zero_of_getElem? _ 7 (inner_length_14 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_14_0 y z w b u
  · exact coefficient_14_1 y z w b u
  · exact coefficient_14_2 y z w b u
  · exact coefficient_14_3 y z w b u
  · exact coefficient_14_4 y z w b u
  · exact coefficient_14_5 y z w b u
  · exact coefficient_14_6 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 14 through 14 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_15 (y z w b u : ℂ) : ∀ v∈innerCertificate15 y z w b u,v=0 := by
  apply zero_of_getElem? _ 6 (inner_length_15 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_15_0 y z w b u
  · exact coefficient_15_1 y z w b u
  · exact coefficient_15_2 y z w b u
  · exact coefficient_15_3 y z w b u
  · exact coefficient_15_4 y z w b u
  · exact coefficient_15_5 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 15 through 15 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_16 (y z w b u : ℂ) : ∀ v∈innerCertificate16 y z w b u,v=0 := by
  apply zero_of_getElem? _ 5 (inner_length_16 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_16_0 y z w b u
  · exact coefficient_16_1 y z w b u
  · exact coefficient_16_2 y z w b u
  · exact coefficient_16_3 y z w b u
  · exact coefficient_16_4 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 16 through 16 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_17 (y z w b u : ℂ) : ∀ v∈innerCertificate17 y z w b u,v=0 := by
  apply zero_of_getElem? _ 5 (inner_length_17 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_17_0 y z w b u
  · exact coefficient_17_1 y z w b u
  · exact coefficient_17_2 y z w b u
  · exact coefficient_17_3 y z w b u
  · exact coefficient_17_4 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 17 through 17 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_18 (y z w b u : ℂ) : ∀ v∈innerCertificate18 y z w b u,v=0 := by
  apply zero_of_getElem? _ 4 (inner_length_18 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_18_0 y z w b u
  · exact coefficient_18_1 y z w b u
  · exact coefficient_18_2 y z w b u
  · exact coefficient_18_3 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 18 through 18 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_19 (y z w b u : ℂ) : ∀ v∈innerCertificate19 y z w b u,v=0 := by
  apply zero_of_getElem? _ 3 (inner_length_19 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_19_0 y z w b u
  · exact coefficient_19_1 y z w b u
  · exact coefficient_19_2 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 19 through 19 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_20 (y z w b u : ℂ) : ∀ v∈innerCertificate20 y z w b u,v=0 := by
  apply zero_of_getElem? _ 2 (inner_length_20 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_20_0 y z w b u
  · exact coefficient_20_1 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 20 through 20 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_21 (y z w b u : ℂ) : ∀ v∈innerCertificate21 y z w b u,v=0 := by
  apply zero_of_getElem? _ 1 (inner_length_21 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_21_0 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 21 through 21 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, coefficients4, coefficients5, coefficients6, certificate]

end SmallLevelTwentySixMMPPariTrace024
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace024
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_zero (y z w a b u : ℂ) : ∀ v∈certificate y z w a b u,v=0 := by
  apply zero_of_getElem? _ 22 (certificate_length y z w a b u)
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
compact_certificate_declaration theorem identity (x y z w a b u : ℂ) :
    p0 x y z w a b u*p1 x y z w a b u+p2 x y z w a b u*p3 x y z w a b u=p4 x y z w a b u+p5 x y z w a b u*p6 x y z w a b u := by
  unfold p0 p1 p2 p3 p4 p5 p6
  exact of_zero_coefficients x _ _ _ _ _ _ _ (certificate_zero y z w a b u)
#print axioms identity

end SmallLevelTwentySixMMPPariTrace024
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

namespace SmallLevelTwentySixMMPPariTrace025
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_length (y z w a b u : ℂ) : (certificate y z w a b u).length=22 := by
  norm_num [certificate,add,multiply,scale,coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6]

end SmallLevelTwentySixMMPPariTrace025
end

section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

namespace SmallLevelTwentySixMMPPariTrace025
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem identity_shift (x y z w a b u : ℂ) :
    p0 x y z w a b u*p1 x y z w a b u+p2 x y z w a b u*p3 x y z w a b u=
      p4 x y z w a b u+p5 x y z w a b u*p6 x y z w a b u := by
  have h0 : p0 x y z w a b u=1 := by norm_num [p0,coefficients0,c0_0,evaluate]
  have h2 : p2 x y z w a b u=0 := by norm_num [p2,coefficients2,evaluate]
  have h4 : p4 x y z w a b u=0 := by norm_num [p4,coefficients4,evaluate]
  have h5 : p5 x y z w a b u=x^2 := by
    simp only [p5,coefficients5,c5_0,c5_1,c5_2,evaluate]
    ring
  have hcoeff : coefficients1 y z w a b u=List.replicate 2 0 ++ coefficients6 y z w a b u := by rfl
  rw [h0,h2,h4,h5]
  simp only [one_mul,zero_mul,zero_add,add_zero]
  unfold p1 p6
  rw [hcoeff]
  exact SmallLevelPolynomialZeroPrefix.evaluate_zero_prefix x _ _
#print axioms identity_shift
end SmallLevelTwentySixMMPPariTrace025
end
end

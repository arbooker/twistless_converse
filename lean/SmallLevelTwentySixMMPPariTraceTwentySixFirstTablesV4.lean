module
public import SmallLevelTwentySixMMPPariTraceTwentyFourV4
public import SmallLevelTwentySixInnerTraceTwentySixV1
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
  simp only [certificate, length_add, length_multiply, length_scale]
  norm_num [coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6, List.length_cons, List.length_nil]

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
  simp only [innerCertificate0, length_add, length_multiply, length_scale]
  norm_num [inner0_0,inner1_0,inner2_0,inner3_0,inner4_0, List.length_cons, List.length_nil]
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
  simp only [innerCertificate1, length_add, length_multiply, length_scale]
  norm_num [inner0_0,inner0_1,inner1_0,inner1_1,inner2_0,inner2_1,inner3_0,inner3_1,inner4_1, List.length_cons, List.length_nil]
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
  simp only [innerCertificate2, length_add, length_multiply, length_scale]
  norm_num [inner0_0,inner0_1,inner0_2,inner1_0,inner1_1,inner1_2,inner2_0,inner2_1,inner2_2,inner3_0,inner3_1,inner3_2,inner4_2, List.length_cons, List.length_nil]
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
  simp only [innerCertificate3, length_add, length_multiply, length_scale]
  norm_num [inner0_0,inner0_1,inner0_2,inner0_3,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner3_0,inner3_1,inner3_2,inner3_3,inner4_3, List.length_cons, List.length_nil]
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
  simp only [innerCertificate4, length_add, length_multiply, length_scale]
  norm_num [inner0_1,inner0_2,inner0_3,inner0_4,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner4_4, List.length_cons, List.length_nil]
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
  simp only [innerCertificate5, length_add, length_multiply, length_scale]
  norm_num [inner0_2,inner0_3,inner0_4,inner0_5,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner4_5, List.length_cons, List.length_nil]
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
  simp only [innerCertificate6, length_add, length_multiply, length_scale]
  norm_num [inner0_3,inner0_4,inner0_5,inner0_6,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner4_6, List.length_cons, List.length_nil]
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
  simp only [innerCertificate7, length_add, length_multiply, length_scale]
  norm_num [inner0_4,inner0_5,inner0_6,inner0_7,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner4_7, List.length_cons, List.length_nil]
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

end SmallLevelTwentySixMMPPariTrace026
end

end

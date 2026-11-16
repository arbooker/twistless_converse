module
public import SmallLevelTwentySixMMPPariTraceInitialV4
public import SmallLevelTwentySixRationalTraceTwentyV1
public import SmallLevelTwentySixRationalTraceEighteenV1
public import SmallLevelTwentySixSparseTraceSixteenV1
public import SmallLevelTwentySixInnerTraceFourteenV1
public import SmallLevelTwentySixCachedASTTraceTwentyTwoV1
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
  simp only [certificate, length_add, length_multiply, length_scale]
  norm_num [coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6, List.length_cons, List.length_nil]

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
  simp only [innerCertificate0, length_add, length_multiply, length_scale]
  norm_num [inner0_0,inner1_0,inner2_0,inner3_0,inner4_0, List.length_cons, List.length_nil]
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
  simp only [innerCertificate1, length_add, length_multiply, length_scale]
  norm_num [inner0_0,inner0_1,inner1_0,inner1_1,inner2_0,inner2_1,inner3_0,inner3_1,inner4_1, List.length_cons, List.length_nil]
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
  simp only [innerCertificate2, length_add, length_multiply, length_scale]
  norm_num [inner0_0,inner0_1,inner0_2,inner1_0,inner1_1,inner1_2,inner2_0,inner2_1,inner2_2,inner3_0,inner3_1,inner3_2,inner4_2, List.length_cons, List.length_nil]
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
  simp only [innerCertificate3, length_add, length_multiply, length_scale]
  norm_num [inner0_0,inner0_1,inner0_2,inner0_3,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner3_0,inner3_1,inner3_2,inner3_3,inner4_3, List.length_cons, List.length_nil]
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
  simp only [innerCertificate4, length_add, length_multiply, length_scale]
  norm_num [inner0_1,inner0_2,inner0_3,inner0_4,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner4_4, List.length_cons, List.length_nil]
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
  simp only [innerCertificate5, length_add, length_multiply, length_scale]
  norm_num [inner0_2,inner0_3,inner0_4,inner0_5,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner4_5, List.length_cons, List.length_nil]
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
  simp only [innerCertificate6, length_add, length_multiply, length_scale]
  norm_num [inner0_3,inner0_4,inner0_5,inner0_6,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner4_6, List.length_cons, List.length_nil]
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
  simp only [innerCertificate7, length_add, length_multiply, length_scale]
  norm_num [inner0_4,inner0_5,inner0_6,inner0_7,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner4_7, List.length_cons, List.length_nil]
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
  simp only [innerCertificate8, length_add, length_multiply, length_scale]
  norm_num [inner0_5,inner0_6,inner0_7,inner0_8,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner4_8, List.length_cons, List.length_nil]
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
  simp only [innerCertificate9, length_add, length_multiply, length_scale]
  norm_num [inner0_6,inner0_7,inner0_8,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner3_9,inner4_9, List.length_cons, List.length_nil]
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
  simp only [innerCertificate10, length_add, length_multiply, length_scale]
  norm_num [inner0_10,inner0_7,inner0_8,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_10,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner3_9,inner4_10, List.length_cons, List.length_nil]
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
  simp only [innerCertificate11, length_add, length_multiply, length_scale]
  norm_num [inner0_10,inner0_11,inner0_8,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_10,inner3_11,inner3_5,inner3_6,inner3_7,inner3_8,inner3_9,inner4_11, List.length_cons, List.length_nil]
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
  simp only [innerCertificate12, length_add, length_multiply, length_scale]
  norm_num [inner0_10,inner0_11,inner0_12,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_10,inner3_11,inner3_12,inner3_6,inner3_7,inner3_8,inner3_9,inner4_12, List.length_cons, List.length_nil]
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
  simp only [innerCertificate13, length_add, length_multiply, length_scale]
  norm_num [inner0_10,inner0_11,inner0_12,inner0_13,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_10,inner3_11,inner3_12,inner3_13,inner3_7,inner3_8,inner3_9,inner4_13, List.length_cons, List.length_nil]
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
  simp only [innerCertificate14, length_add, length_multiply, length_scale]
  norm_num [inner0_11,inner0_12,inner0_13,inner0_14,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_8,inner3_9,inner4_14, List.length_cons, List.length_nil]
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
  simp only [innerCertificate15, length_add, length_multiply, length_scale]
  norm_num [inner0_12,inner0_13,inner0_14,inner0_15,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_9,inner4_15, List.length_cons, List.length_nil]
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
  simp only [innerCertificate16, length_add, length_multiply, length_scale]
  norm_num [inner0_13,inner0_14,inner0_15,inner0_16,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner4_16, List.length_cons, List.length_nil]
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
  simp only [innerCertificate17, length_add, length_multiply, length_scale]
  norm_num [inner0_14,inner0_15,inner0_16,inner0_17,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner4_17, List.length_cons, List.length_nil]
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
  simp only [innerCertificate18, length_add, length_multiply, length_scale]
  norm_num [inner0_15,inner0_16,inner0_17,inner0_18,inner1_0,inner1_1,inner1_2,inner1_3,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner4_18, List.length_cons, List.length_nil]
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
  simp only [innerCertificate19, length_add, length_multiply, length_scale]
  norm_num [inner0_16,inner0_17,inner0_18,inner0_19,inner1_0,inner1_1,inner1_2,inner1_3,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner4_19, List.length_cons, List.length_nil]
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
  simp only [innerCertificate20, length_add, length_multiply, length_scale]
  norm_num [inner0_17,inner0_18,inner0_19,inner0_20,inner1_0,inner1_1,inner1_2,inner1_3,inner2_3,inner2_4,inner2_5,inner2_6,inner3_14,inner3_15,inner3_16,inner3_17,inner4_20, List.length_cons, List.length_nil]
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
  simp only [innerCertificate21, length_add, length_multiply, length_scale]
  norm_num [inner0_18,inner0_19,inner0_20,inner0_21,inner1_0,inner1_1,inner1_2,inner1_3,inner2_4,inner2_5,inner2_6,inner3_15,inner3_16,inner3_17,inner4_21, List.length_cons, List.length_nil]
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
  simp only [innerCertificate22, length_add, length_multiply, length_scale]
  norm_num [inner0_19,inner0_20,inner0_21,inner1_1,inner1_2,inner1_3,inner2_5,inner2_6,inner3_16,inner3_17,inner4_22, List.length_cons, List.length_nil]
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
  simp only [innerCertificate23, length_add, length_multiply, length_scale]
  norm_num [inner0_20,inner0_21,inner1_2,inner1_3,inner2_6,inner3_17,inner4_23, List.length_cons, List.length_nil]
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
  simp only [innerCertificate24, length_add, length_multiply, length_scale]
  norm_num [inner0_21,inner1_3,inner4_24, List.length_cons, List.length_nil]
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
  simp only [certificate, length_add, length_multiply, length_scale]
  norm_num [coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6, List.length_cons, List.length_nil]

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


end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/

end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false


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
  simp only [certificate, length_add, length_multiply, length_scale]
  norm_num [coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6, List.length_cons, List.length_nil]

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


end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/

end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false


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


end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/

end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false


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


end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/

end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false


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
  simp only [certificate, length_add, length_multiply, length_scale]
  norm_num [coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6, List.length_cons, List.length_nil]

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


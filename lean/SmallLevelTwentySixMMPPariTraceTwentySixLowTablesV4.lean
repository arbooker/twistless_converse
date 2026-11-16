module
public import SmallLevelTwentySixMMPPariTraceTwentySixFirstTablesV4
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
compact_certificate_declaration theorem inner_length_8 (y z w b u : ℂ) : (innerCertificate8 y z w b u).length=15 := by
  simp only [innerCertificate8, length_add, length_multiply, length_scale]
  norm_num [inner0_5,inner0_6,inner0_7,inner0_8,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner4_8, List.length_cons, List.length_nil]
compact_certificate_declaration theorem inner_eval_8 (y z w a b u : ℂ) :
    evaluate a (innerCertificate8 y z w b u)=(((((c0_5 y z w a b u)*(c1_3 y z w a b u))+(((c0_6 y z w a b u)*(c1_2 y z w a b u))+(((c0_7 y z w a b u)*(c1_1 y z w a b u))+(((c0_8 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_8 y z w a b u))+(((c2_1 y z w a b u)*(c3_7 y z w a b u))+(((c2_2 y z w a b u)*(c3_6 y z w a b u))+(((c2_3 y z w a b u)*(c3_5 y z w a b u))+(((c2_4 y z w a b u)*(c3_4 y z w a b u))+(((c2_5 y z w a b u)*(c3_3 y z w a b u))+(((c2_6 y z w a b u)*(c3_2 y z w a b u))+(((c2_7 y z w a b u)*(c3_1 y z w a b u))+(((c2_8 y z w a b u)*(c3_0 y z w a b u))+0))))))))))+((-1)*(c4_8 y z w a b u))) := by
  simp only [innerCertificate8,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_5,c0_6,c0_7,c0_8,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c3_0,c3_1,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c4_8]
#print axioms inner_eval_8

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
compact_certificate_declaration theorem inner_length_9 (y z w b u : ℂ) : (innerCertificate9 y z w b u).length=15 := by
  simp only [innerCertificate9, length_add, length_multiply, length_scale]
  norm_num [inner0_6,inner0_7,inner0_8,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner3_9,inner4_9, List.length_cons, List.length_nil]
compact_certificate_declaration theorem inner_eval_9 (y z w a b u : ℂ) :
    evaluate a (innerCertificate9 y z w b u)=(((((c0_6 y z w a b u)*(c1_3 y z w a b u))+(((c0_7 y z w a b u)*(c1_2 y z w a b u))+(((c0_8 y z w a b u)*(c1_1 y z w a b u))+(((c0_9 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_9 y z w a b u))+(((c2_1 y z w a b u)*(c3_8 y z w a b u))+(((c2_2 y z w a b u)*(c3_7 y z w a b u))+(((c2_3 y z w a b u)*(c3_6 y z w a b u))+(((c2_4 y z w a b u)*(c3_5 y z w a b u))+(((c2_5 y z w a b u)*(c3_4 y z w a b u))+(((c2_6 y z w a b u)*(c3_3 y z w a b u))+(((c2_7 y z w a b u)*(c3_2 y z w a b u))+(((c2_8 y z w a b u)*(c3_1 y z w a b u))+(((c2_9 y z w a b u)*(c3_0 y z w a b u))+0)))))))))))+((-1)*(c4_9 y z w a b u))) := by
  simp only [innerCertificate9,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_6,c0_7,c0_8,c0_9,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_9]
#print axioms inner_eval_9

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
compact_certificate_declaration theorem inner_length_10 (y z w b u : ℂ) : (innerCertificate10 y z w b u).length=15 := by
  simp only [innerCertificate10, length_add, length_multiply, length_scale]
  norm_num [inner0_10,inner0_7,inner0_8,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_0,inner3_1,inner3_10,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner3_9,inner4_10, List.length_cons, List.length_nil]
compact_certificate_declaration theorem inner_eval_10 (y z w a b u : ℂ) :
    evaluate a (innerCertificate10 y z w b u)=(((((c0_7 y z w a b u)*(c1_3 y z w a b u))+(((c0_8 y z w a b u)*(c1_2 y z w a b u))+(((c0_9 y z w a b u)*(c1_1 y z w a b u))+(((c0_10 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_10 y z w a b u))+(((c2_1 y z w a b u)*(c3_9 y z w a b u))+(((c2_2 y z w a b u)*(c3_8 y z w a b u))+(((c2_3 y z w a b u)*(c3_7 y z w a b u))+(((c2_4 y z w a b u)*(c3_6 y z w a b u))+(((c2_5 y z w a b u)*(c3_5 y z w a b u))+(((c2_6 y z w a b u)*(c3_4 y z w a b u))+(((c2_7 y z w a b u)*(c3_3 y z w a b u))+(((c2_8 y z w a b u)*(c3_2 y z w a b u))+(((c2_9 y z w a b u)*(c3_1 y z w a b u))+(((c2_10 y z w a b u)*(c3_0 y z w a b u))+0))))))))))))+((-1)*(c4_10 y z w a b u))) := by
  simp only [innerCertificate10,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_10,c0_7,c0_8,c0_9,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_10,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_10,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_10]
#print axioms inner_eval_10

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
compact_certificate_declaration theorem inner_length_11 (y z w b u : ℂ) : (innerCertificate11 y z w b u).length=15 := by
  simp only [innerCertificate11, length_add, length_multiply, length_scale]
  norm_num [inner0_10,inner0_11,inner0_8,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_1,inner3_10,inner3_11,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner3_9,inner4_11, List.length_cons, List.length_nil]
compact_certificate_declaration theorem inner_eval_11 (y z w a b u : ℂ) :
    evaluate a (innerCertificate11 y z w b u)=(((((c0_8 y z w a b u)*(c1_3 y z w a b u))+(((c0_9 y z w a b u)*(c1_2 y z w a b u))+(((c0_10 y z w a b u)*(c1_1 y z w a b u))+(((c0_11 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_11 y z w a b u))+(((c2_1 y z w a b u)*(c3_10 y z w a b u))+(((c2_2 y z w a b u)*(c3_9 y z w a b u))+(((c2_3 y z w a b u)*(c3_8 y z w a b u))+(((c2_4 y z w a b u)*(c3_7 y z w a b u))+(((c2_5 y z w a b u)*(c3_6 y z w a b u))+(((c2_6 y z w a b u)*(c3_5 y z w a b u))+(((c2_7 y z w a b u)*(c3_4 y z w a b u))+(((c2_8 y z w a b u)*(c3_3 y z w a b u))+(((c2_9 y z w a b u)*(c3_2 y z w a b u))+((c2_10 y z w a b u)*(c3_1 y z w a b u)))))))))))))+((-1)*(c4_11 y z w a b u))) := by
  simp only [innerCertificate11,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_10,c0_11,c0_8,c0_9,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_10,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_1,c3_10,c3_11,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_11]
#print axioms inner_eval_11

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
compact_certificate_declaration theorem inner_length_12 (y z w b u : ℂ) : (innerCertificate12 y z w b u).length=15 := by
  simp only [innerCertificate12, length_add, length_multiply, length_scale]
  norm_num [inner0_10,inner0_11,inner0_12,inner0_9,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_10,inner3_11,inner3_12,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner3_9,inner4_12, List.length_cons, List.length_nil]
compact_certificate_declaration theorem inner_eval_12 (y z w a b u : ℂ) :
    evaluate a (innerCertificate12 y z w b u)=(((((c0_9 y z w a b u)*(c1_3 y z w a b u))+(((c0_10 y z w a b u)*(c1_2 y z w a b u))+(((c0_11 y z w a b u)*(c1_1 y z w a b u))+(((c0_12 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_12 y z w a b u))+(((c2_1 y z w a b u)*(c3_11 y z w a b u))+(((c2_2 y z w a b u)*(c3_10 y z w a b u))+(((c2_3 y z w a b u)*(c3_9 y z w a b u))+(((c2_4 y z w a b u)*(c3_8 y z w a b u))+(((c2_5 y z w a b u)*(c3_7 y z w a b u))+(((c2_6 y z w a b u)*(c3_6 y z w a b u))+(((c2_7 y z w a b u)*(c3_5 y z w a b u))+(((c2_8 y z w a b u)*(c3_4 y z w a b u))+(((c2_9 y z w a b u)*(c3_3 y z w a b u))+((c2_10 y z w a b u)*(c3_2 y z w a b u)))))))))))))+((-1)*(c4_12 y z w a b u))) := by
  simp only [innerCertificate12,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_10,c0_11,c0_12,c0_9,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_10,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_10,c3_11,c3_12,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_12]
#print axioms inner_eval_12

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
compact_certificate_declaration theorem inner_length_13 (y z w b u : ℂ) : (innerCertificate13 y z w b u).length=14 := by
  simp only [innerCertificate13, length_add, length_multiply, length_scale]
  norm_num [inner0_10,inner0_11,inner0_12,inner0_13,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_10,inner3_11,inner3_12,inner3_13,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner3_9,inner4_13, List.length_cons, List.length_nil]
compact_certificate_declaration theorem inner_eval_13 (y z w a b u : ℂ) :
    evaluate a (innerCertificate13 y z w b u)=(((((c0_10 y z w a b u)*(c1_3 y z w a b u))+(((c0_11 y z w a b u)*(c1_2 y z w a b u))+(((c0_12 y z w a b u)*(c1_1 y z w a b u))+(((c0_13 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_13 y z w a b u))+(((c2_1 y z w a b u)*(c3_12 y z w a b u))+(((c2_2 y z w a b u)*(c3_11 y z w a b u))+(((c2_3 y z w a b u)*(c3_10 y z w a b u))+(((c2_4 y z w a b u)*(c3_9 y z w a b u))+(((c2_5 y z w a b u)*(c3_8 y z w a b u))+(((c2_6 y z w a b u)*(c3_7 y z w a b u))+(((c2_7 y z w a b u)*(c3_6 y z w a b u))+(((c2_8 y z w a b u)*(c3_5 y z w a b u))+(((c2_9 y z w a b u)*(c3_4 y z w a b u))+((c2_10 y z w a b u)*(c3_3 y z w a b u)))))))))))))+((-1)*(c4_13 y z w a b u))) := by
  simp only [innerCertificate13,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_10,c0_11,c0_12,c0_13,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_10,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_10,c3_11,c3_12,c3_13,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_13]
#print axioms inner_eval_13

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
compact_certificate_declaration theorem inner_length_14 (y z w b u : ℂ) : (innerCertificate14 y z w b u).length=14 := by
  simp only [innerCertificate14, length_add, length_multiply, length_scale]
  norm_num [inner0_11,inner0_12,inner0_13,inner0_14,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner3_9,inner4_14, List.length_cons, List.length_nil]
compact_certificate_declaration theorem inner_eval_14 (y z w a b u : ℂ) :
    evaluate a (innerCertificate14 y z w b u)=(((((c0_11 y z w a b u)*(c1_3 y z w a b u))+(((c0_12 y z w a b u)*(c1_2 y z w a b u))+(((c0_13 y z w a b u)*(c1_1 y z w a b u))+(((c0_14 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_14 y z w a b u))+(((c2_1 y z w a b u)*(c3_13 y z w a b u))+(((c2_2 y z w a b u)*(c3_12 y z w a b u))+(((c2_3 y z w a b u)*(c3_11 y z w a b u))+(((c2_4 y z w a b u)*(c3_10 y z w a b u))+(((c2_5 y z w a b u)*(c3_9 y z w a b u))+(((c2_6 y z w a b u)*(c3_8 y z w a b u))+(((c2_7 y z w a b u)*(c3_7 y z w a b u))+(((c2_8 y z w a b u)*(c3_6 y z w a b u))+(((c2_9 y z w a b u)*(c3_5 y z w a b u))+((c2_10 y z w a b u)*(c3_4 y z w a b u)))))))))))))+((-1)*(c4_14 y z w a b u))) := by
  simp only [innerCertificate14,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_11,c0_12,c0_13,c0_14,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_10,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_10,c3_11,c3_12,c3_13,c3_14,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_14]
#print axioms inner_eval_14

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
compact_certificate_declaration theorem inner_length_15 (y z w b u : ℂ) : (innerCertificate15 y z w b u).length=13 := by
  simp only [innerCertificate15, length_add, length_multiply, length_scale]
  norm_num [inner0_12,inner0_13,inner0_14,inner0_15,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_5,inner3_6,inner3_7,inner3_8,inner3_9,inner4_15, List.length_cons, List.length_nil]
compact_certificate_declaration theorem inner_eval_15 (y z w a b u : ℂ) :
    evaluate a (innerCertificate15 y z w b u)=(((((c0_12 y z w a b u)*(c1_3 y z w a b u))+(((c0_13 y z w a b u)*(c1_2 y z w a b u))+(((c0_14 y z w a b u)*(c1_1 y z w a b u))+(((c0_15 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_15 y z w a b u))+(((c2_1 y z w a b u)*(c3_14 y z w a b u))+(((c2_2 y z w a b u)*(c3_13 y z w a b u))+(((c2_3 y z w a b u)*(c3_12 y z w a b u))+(((c2_4 y z w a b u)*(c3_11 y z w a b u))+(((c2_5 y z w a b u)*(c3_10 y z w a b u))+(((c2_6 y z w a b u)*(c3_9 y z w a b u))+(((c2_7 y z w a b u)*(c3_8 y z w a b u))+(((c2_8 y z w a b u)*(c3_7 y z w a b u))+(((c2_9 y z w a b u)*(c3_6 y z w a b u))+((c2_10 y z w a b u)*(c3_5 y z w a b u)))))))))))))+((-1)*(c4_15 y z w a b u))) := by
  simp only [innerCertificate15,evaluate_add,evaluate_multiply,evaluate,
    mul_zero,add_zero,zero_add,c0_12,c0_13,c0_14,c0_15,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_10,c2_2,c2_3,c2_4,c2_5,c2_6,c2_7,c2_8,c2_9,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_5,c3_6,c3_7,c3_8,c3_9,c4_15]
#print axioms inner_eval_15

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

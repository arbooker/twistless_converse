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
  simp only [innerCertificate16, length_add, length_multiply, length_scale]
  norm_num [inner0_13,inner0_14,inner0_15,inner0_16,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_6,inner3_7,inner3_8,inner3_9,inner4_16, List.length_cons, List.length_nil]
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
  simp only [innerCertificate17, length_add, length_multiply, length_scale]
  norm_num [inner0_14,inner0_15,inner0_16,inner0_17,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner3_7,inner3_8,inner3_9,inner4_17, List.length_cons, List.length_nil]
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
  simp only [innerCertificate18, length_add, length_multiply, length_scale]
  norm_num [inner0_15,inner0_16,inner0_17,inner0_18,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner3_18,inner3_8,inner3_9,inner4_18, List.length_cons, List.length_nil]
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
  simp only [innerCertificate19, length_add, length_multiply, length_scale]
  norm_num [inner0_16,inner0_17,inner0_18,inner0_19,inner1_0,inner1_1,inner1_2,inner1_3,inner2_0,inner2_1,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner3_18,inner3_19,inner3_9,inner4_19, List.length_cons, List.length_nil]
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
  simp only [innerCertificate20, length_add, length_multiply, length_scale]
  norm_num [inner0_17,inner0_18,inner0_19,inner0_20,inner1_0,inner1_1,inner1_2,inner1_3,inner2_1,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_10,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner3_18,inner3_19,inner4_20, List.length_cons, List.length_nil]
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
  simp only [innerCertificate21, length_add, length_multiply, length_scale]
  norm_num [inner0_18,inner0_19,inner0_20,inner0_21,inner1_0,inner1_1,inner1_2,inner1_3,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_11,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner3_18,inner3_19,inner4_21, List.length_cons, List.length_nil]
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
  simp only [innerCertificate22, length_add, length_multiply, length_scale]
  norm_num [inner0_19,inner0_20,inner0_21,inner0_22,inner1_0,inner1_1,inner1_2,inner1_3,inner2_10,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_12,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner3_18,inner3_19,inner4_22, List.length_cons, List.length_nil]
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
  simp only [innerCertificate23, length_add, length_multiply, length_scale]
  norm_num [inner0_20,inner0_21,inner0_22,inner0_23,inner1_0,inner1_1,inner1_2,inner1_3,inner2_10,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_13,inner3_14,inner3_15,inner3_16,inner3_17,inner3_18,inner3_19,inner4_23, List.length_cons, List.length_nil]
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

end SmallLevelTwentySixMMPPariTrace026
end

end

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
  simp only [innerCertificate24, length_add, length_multiply, length_scale]
  norm_num [inner0_21,inner0_22,inner0_23,inner0_24,inner1_0,inner1_1,inner1_2,inner1_3,inner2_10,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_14,inner3_15,inner3_16,inner3_17,inner3_18,inner3_19,inner4_24, List.length_cons, List.length_nil]
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
  simp only [innerCertificate25, length_add, length_multiply, length_scale]
  norm_num [inner0_22,inner0_23,inner0_24,inner0_25,inner1_0,inner1_1,inner1_2,inner1_3,inner2_10,inner2_6,inner2_7,inner2_8,inner2_9,inner3_15,inner3_16,inner3_17,inner3_18,inner3_19,inner4_25, List.length_cons, List.length_nil]
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
  simp only [innerCertificate26, length_add, length_multiply, length_scale]
  norm_num [inner0_23,inner0_24,inner0_25,inner0_26,inner1_0,inner1_1,inner1_2,inner1_3,inner2_10,inner2_7,inner2_8,inner2_9,inner3_16,inner3_17,inner3_18,inner3_19,inner4_26, List.length_cons, List.length_nil]
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
  simp only [innerCertificate27, length_add, length_multiply, length_scale]
  norm_num [inner0_24,inner0_25,inner0_26,inner0_27,inner1_0,inner1_1,inner1_2,inner1_3,inner2_10,inner2_8,inner2_9,inner3_17,inner3_18,inner3_19,inner4_27, List.length_cons, List.length_nil]
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
  simp only [innerCertificate28, length_add, length_multiply, length_scale]
  norm_num [inner0_25,inner0_26,inner0_27,inner0_28,inner1_0,inner1_1,inner1_2,inner1_3,inner2_10,inner2_9,inner3_18,inner3_19,inner4_28, List.length_cons, List.length_nil]
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
  simp only [innerCertificate29, length_add, length_multiply, length_scale]
  norm_num [inner0_26,inner0_27,inner0_28,inner1_1,inner1_2,inner1_3,inner2_10,inner3_19,inner4_29, List.length_cons, List.length_nil]
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
  simp only [innerCertificate30, length_add, length_multiply, length_scale]
  norm_num [inner0_27,inner0_28,inner1_2,inner1_3,inner4_30, List.length_cons, List.length_nil]
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
  simp only [innerCertificate31, length_add, length_multiply, length_scale]
  norm_num [inner0_28,inner1_3,inner4_31, List.length_cons, List.length_nil]
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
end SmallLevelTwentySixMMPPariTrace026
end

end

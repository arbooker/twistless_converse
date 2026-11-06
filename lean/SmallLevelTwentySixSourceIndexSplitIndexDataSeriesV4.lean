module
public import SmallLevelTwentySixSourceIndexSplitIndexFamilySeriesV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixSource89Split09
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89
def innerCertificate (z w a b u : ℂ) : List ℂ := add (add (add (multiply ((inner0_0 z w a b u)) ((inner1_9 z w a b u))) (add (multiply ((inner0_1 z w a b u)) ((inner1_8 z w a b u))) (add (multiply ((inner0_2 z w a b u)) ((inner1_7 z w a b u))) (multiply ((inner0_3 z w a b u)) ((inner1_6 z w a b u)))))) (add (multiply ((inner2_1 z w a b u)) ((inner3_8 z w a b u))) (add (multiply ((inner2_2 z w a b u)) ((inner3_7 z w a b u))) (add (multiply ((inner2_3 z w a b u)) ((inner3_6 z w a b u))) (add (multiply ((inner2_4 z w a b u)) ((inner3_5 z w a b u))) (add (multiply ((inner2_5 z w a b u)) ((inner3_4 z w a b u))) (add (multiply ((inner2_6 z w a b u)) ((inner3_3 z w a b u))) (add (multiply ((inner2_7 z w a b u)) ((inner3_2 z w a b u))) (add (multiply ((inner2_8 z w a b u)) ((inner3_1 z w a b u))) (add (multiply ((inner2_9 z w a b u)) ((inner3_0 z w a b u))) ([]))))))))))) (multiply ([(-1)]) ((inner4_9 z w a b u)))
theorem inner_length (z w a b u : ℂ) : (innerCertificate z w a b u).length=9 := by
  norm_num [innerCertificate,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner0_3,inner1_6,inner1_7,inner1_8,inner1_9,inner2_1,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner4_9]
theorem inner_eval (y z w a b u : ℂ) : evaluate y (innerCertificate z w a b u)=(((((c0_0 y z w a b u)*(c1_9 y z w a b u))+(((c0_1 y z w a b u)*(c1_8 y z w a b u))+(((c0_2 y z w a b u)*(c1_7 y z w a b u))+((c0_3 y z w a b u)*(c1_6 y z w a b u)))))+(((c2_1 y z w a b u)*(c3_8 y z w a b u))+(((c2_2 y z w a b u)*(c3_7 y z w a b u))+(((c2_3 y z w a b u)*(c3_6 y z w a b u))+(((c2_4 y z w a b u)*(c3_5 y z w a b u))+(((c2_5 y z w a b u)*(c3_4 y z w a b u))+(((c2_6 y z w a b u)*(c3_3 y z w a b u))+(((c2_7 y z w a b u)*(c3_2 y z w a b u))+(((c2_8 y z w a b u)*(c3_1 y z w a b u))+(((c2_9 y z w a b u)*(c3_0 y z w a b u))+0))))))))))+((-1)*(c4_9 y z w a b u))) := by
  simp only [innerCertificate,evaluate_add,evaluate_multiply,bind_c0_0,bind_c0_1,bind_c0_2,bind_c0_3,bind_c1_6,bind_c1_7,bind_c1_8,bind_c1_9,bind_c2_1,bind_c2_2,bind_c2_3,bind_c2_4,bind_c2_5,bind_c2_6,bind_c2_7,bind_c2_8,bind_c2_9,bind_c3_0,bind_c3_1,bind_c3_2,bind_c3_3,bind_c3_4,bind_c3_5,bind_c3_6,bind_c3_7,bind_c3_8,bind_c4_9,evaluate,mul_zero,add_zero,zero_add]

end SmallLevelTwentySixSource89Split09
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixSource89Split10
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89
def innerCertificate (z w a b u : ℂ) : List ℂ := add (add (add (multiply ((inner0_0 z w a b u)) ((inner1_10 z w a b u))) (add (multiply ((inner0_1 z w a b u)) ((inner1_9 z w a b u))) (add (multiply ((inner0_2 z w a b u)) ((inner1_8 z w a b u))) (multiply ((inner0_3 z w a b u)) ((inner1_7 z w a b u)))))) (add (multiply ((inner2_2 z w a b u)) ((inner3_8 z w a b u))) (add (multiply ((inner2_3 z w a b u)) ((inner3_7 z w a b u))) (add (multiply ((inner2_4 z w a b u)) ((inner3_6 z w a b u))) (add (multiply ((inner2_5 z w a b u)) ((inner3_5 z w a b u))) (add (multiply ((inner2_6 z w a b u)) ((inner3_4 z w a b u))) (add (multiply ((inner2_7 z w a b u)) ((inner3_3 z w a b u))) (add (multiply ((inner2_8 z w a b u)) ((inner3_2 z w a b u))) (add (multiply ((inner2_9 z w a b u)) ((inner3_1 z w a b u))) (add (multiply ((inner2_10 z w a b u)) ((inner3_0 z w a b u))) ([]))))))))))) (multiply ([(-1)]) ((inner4_10 z w a b u)))
theorem inner_length (z w a b u : ℂ) : (innerCertificate z w a b u).length=9 := by
  norm_num [innerCertificate,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner0_3,inner1_10,inner1_7,inner1_8,inner1_9,inner2_10,inner2_2,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner4_10]
theorem inner_eval (y z w a b u : ℂ) : evaluate y (innerCertificate z w a b u)=(((((c0_0 y z w a b u)*(c1_10 y z w a b u))+(((c0_1 y z w a b u)*(c1_9 y z w a b u))+(((c0_2 y z w a b u)*(c1_8 y z w a b u))+((c0_3 y z w a b u)*(c1_7 y z w a b u)))))+(((c2_2 y z w a b u)*(c3_8 y z w a b u))+(((c2_3 y z w a b u)*(c3_7 y z w a b u))+(((c2_4 y z w a b u)*(c3_6 y z w a b u))+(((c2_5 y z w a b u)*(c3_5 y z w a b u))+(((c2_6 y z w a b u)*(c3_4 y z w a b u))+(((c2_7 y z w a b u)*(c3_3 y z w a b u))+(((c2_8 y z w a b u)*(c3_2 y z w a b u))+(((c2_9 y z w a b u)*(c3_1 y z w a b u))+(((c2_10 y z w a b u)*(c3_0 y z w a b u))+0))))))))))+((-1)*(c4_10 y z w a b u))) := by
  simp only [innerCertificate,evaluate_add,evaluate_multiply,bind_c0_0,bind_c0_1,bind_c0_2,bind_c0_3,bind_c1_10,bind_c1_7,bind_c1_8,bind_c1_9,bind_c2_10,bind_c2_2,bind_c2_3,bind_c2_4,bind_c2_5,bind_c2_6,bind_c2_7,bind_c2_8,bind_c2_9,bind_c3_0,bind_c3_1,bind_c3_2,bind_c3_3,bind_c3_4,bind_c3_5,bind_c3_6,bind_c3_7,bind_c3_8,bind_c4_10,evaluate,mul_zero,add_zero,zero_add]

end SmallLevelTwentySixSource89Split10
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixSource89Split11
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89
def innerCertificate (z w a b u : ℂ) : List ℂ := add (add (add (multiply ((inner0_0 z w a b u)) ((inner1_11 z w a b u))) (add (multiply ((inner0_1 z w a b u)) ((inner1_10 z w a b u))) (add (multiply ((inner0_2 z w a b u)) ((inner1_9 z w a b u))) (multiply ((inner0_3 z w a b u)) ((inner1_8 z w a b u)))))) (add (multiply ((inner2_3 z w a b u)) ((inner3_8 z w a b u))) (add (multiply ((inner2_4 z w a b u)) ((inner3_7 z w a b u))) (add (multiply ((inner2_5 z w a b u)) ((inner3_6 z w a b u))) (add (multiply ((inner2_6 z w a b u)) ((inner3_5 z w a b u))) (add (multiply ((inner2_7 z w a b u)) ((inner3_4 z w a b u))) (add (multiply ((inner2_8 z w a b u)) ((inner3_3 z w a b u))) (add (multiply ((inner2_9 z w a b u)) ((inner3_2 z w a b u))) (add (multiply ((inner2_10 z w a b u)) ((inner3_1 z w a b u))) (add (multiply ((inner2_11 z w a b u)) ((inner3_0 z w a b u))) ([]))))))))))) (multiply ([(-1)]) ((inner4_11 z w a b u)))
theorem inner_length (z w a b u : ℂ) : (innerCertificate z w a b u).length=9 := by
  norm_num [innerCertificate,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner0_3,inner1_10,inner1_11,inner1_8,inner1_9,inner2_10,inner2_11,inner2_3,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner4_11]
theorem inner_eval (y z w a b u : ℂ) : evaluate y (innerCertificate z w a b u)=(((((c0_0 y z w a b u)*(c1_11 y z w a b u))+(((c0_1 y z w a b u)*(c1_10 y z w a b u))+(((c0_2 y z w a b u)*(c1_9 y z w a b u))+((c0_3 y z w a b u)*(c1_8 y z w a b u)))))+(((c2_3 y z w a b u)*(c3_8 y z w a b u))+(((c2_4 y z w a b u)*(c3_7 y z w a b u))+(((c2_5 y z w a b u)*(c3_6 y z w a b u))+(((c2_6 y z w a b u)*(c3_5 y z w a b u))+(((c2_7 y z w a b u)*(c3_4 y z w a b u))+(((c2_8 y z w a b u)*(c3_3 y z w a b u))+(((c2_9 y z w a b u)*(c3_2 y z w a b u))+(((c2_10 y z w a b u)*(c3_1 y z w a b u))+(((c2_11 y z w a b u)*(c3_0 y z w a b u))+0))))))))))+((-1)*(c4_11 y z w a b u))) := by
  simp only [innerCertificate,evaluate_add,evaluate_multiply,bind_c0_0,bind_c0_1,bind_c0_2,bind_c0_3,bind_c1_10,bind_c1_11,bind_c1_8,bind_c1_9,bind_c2_10,bind_c2_11,bind_c2_3,bind_c2_4,bind_c2_5,bind_c2_6,bind_c2_7,bind_c2_8,bind_c2_9,bind_c3_0,bind_c3_1,bind_c3_2,bind_c3_3,bind_c3_4,bind_c3_5,bind_c3_6,bind_c3_7,bind_c3_8,bind_c4_11,evaluate,mul_zero,add_zero,zero_add]

end SmallLevelTwentySixSource89Split11
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixSource89Split12
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89
def innerCertificate (z w a b u : ℂ) : List ℂ := add (add (add (multiply ((inner0_0 z w a b u)) ((inner1_12 z w a b u))) (add (multiply ((inner0_1 z w a b u)) ((inner1_11 z w a b u))) (add (multiply ((inner0_2 z w a b u)) ((inner1_10 z w a b u))) (multiply ((inner0_3 z w a b u)) ((inner1_9 z w a b u)))))) (add (multiply ((inner2_4 z w a b u)) ((inner3_8 z w a b u))) (add (multiply ((inner2_5 z w a b u)) ((inner3_7 z w a b u))) (add (multiply ((inner2_6 z w a b u)) ((inner3_6 z w a b u))) (add (multiply ((inner2_7 z w a b u)) ((inner3_5 z w a b u))) (add (multiply ((inner2_8 z w a b u)) ((inner3_4 z w a b u))) (add (multiply ((inner2_9 z w a b u)) ((inner3_3 z w a b u))) (add (multiply ((inner2_10 z w a b u)) ((inner3_2 z w a b u))) (add (multiply ((inner2_11 z w a b u)) ((inner3_1 z w a b u))) (add (multiply ((inner2_12 z w a b u)) ((inner3_0 z w a b u))) ([]))))))))))) (multiply ([(-1)]) ((inner4_12 z w a b u)))
theorem inner_length (z w a b u : ℂ) : (innerCertificate z w a b u).length=9 := by
  norm_num [innerCertificate,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner0_3,inner1_10,inner1_11,inner1_12,inner1_9,inner2_10,inner2_11,inner2_12,inner2_4,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner4_12]
theorem inner_eval (y z w a b u : ℂ) : evaluate y (innerCertificate z w a b u)=(((((c0_0 y z w a b u)*(c1_12 y z w a b u))+(((c0_1 y z w a b u)*(c1_11 y z w a b u))+(((c0_2 y z w a b u)*(c1_10 y z w a b u))+((c0_3 y z w a b u)*(c1_9 y z w a b u)))))+(((c2_4 y z w a b u)*(c3_8 y z w a b u))+(((c2_5 y z w a b u)*(c3_7 y z w a b u))+(((c2_6 y z w a b u)*(c3_6 y z w a b u))+(((c2_7 y z w a b u)*(c3_5 y z w a b u))+(((c2_8 y z w a b u)*(c3_4 y z w a b u))+(((c2_9 y z w a b u)*(c3_3 y z w a b u))+(((c2_10 y z w a b u)*(c3_2 y z w a b u))+(((c2_11 y z w a b u)*(c3_1 y z w a b u))+(((c2_12 y z w a b u)*(c3_0 y z w a b u))+0))))))))))+((-1)*(c4_12 y z w a b u))) := by
  simp only [innerCertificate,evaluate_add,evaluate_multiply,bind_c0_0,bind_c0_1,bind_c0_2,bind_c0_3,bind_c1_10,bind_c1_11,bind_c1_12,bind_c1_9,bind_c2_10,bind_c2_11,bind_c2_12,bind_c2_4,bind_c2_5,bind_c2_6,bind_c2_7,bind_c2_8,bind_c2_9,bind_c3_0,bind_c3_1,bind_c3_2,bind_c3_3,bind_c3_4,bind_c3_5,bind_c3_6,bind_c3_7,bind_c3_8,bind_c4_12,evaluate,mul_zero,add_zero,zero_add]

end SmallLevelTwentySixSource89Split12
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixSource89Split13
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89
def innerCertificate (z w a b u : ℂ) : List ℂ := add (add (add (multiply ((inner0_0 z w a b u)) ((inner1_13 z w a b u))) (add (multiply ((inner0_1 z w a b u)) ((inner1_12 z w a b u))) (add (multiply ((inner0_2 z w a b u)) ((inner1_11 z w a b u))) (multiply ((inner0_3 z w a b u)) ((inner1_10 z w a b u)))))) (add (multiply ((inner2_5 z w a b u)) ((inner3_8 z w a b u))) (add (multiply ((inner2_6 z w a b u)) ((inner3_7 z w a b u))) (add (multiply ((inner2_7 z w a b u)) ((inner3_6 z w a b u))) (add (multiply ((inner2_8 z w a b u)) ((inner3_5 z w a b u))) (add (multiply ((inner2_9 z w a b u)) ((inner3_4 z w a b u))) (add (multiply ((inner2_10 z w a b u)) ((inner3_3 z w a b u))) (add (multiply ((inner2_11 z w a b u)) ((inner3_2 z w a b u))) (add (multiply ((inner2_12 z w a b u)) ((inner3_1 z w a b u))) (add (multiply ((inner2_13 z w a b u)) ((inner3_0 z w a b u))) ([]))))))))))) (multiply ([(-1)]) ((inner4_13 z w a b u)))
theorem inner_length (z w a b u : ℂ) : (innerCertificate z w a b u).length=9 := by
  norm_num [innerCertificate,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner0_3,inner1_10,inner1_11,inner1_12,inner1_13,inner2_10,inner2_11,inner2_12,inner2_13,inner2_5,inner2_6,inner2_7,inner2_8,inner2_9,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner4_13]
theorem inner_eval (y z w a b u : ℂ) : evaluate y (innerCertificate z w a b u)=(((((c0_0 y z w a b u)*(c1_13 y z w a b u))+(((c0_1 y z w a b u)*(c1_12 y z w a b u))+(((c0_2 y z w a b u)*(c1_11 y z w a b u))+((c0_3 y z w a b u)*(c1_10 y z w a b u)))))+(((c2_5 y z w a b u)*(c3_8 y z w a b u))+(((c2_6 y z w a b u)*(c3_7 y z w a b u))+(((c2_7 y z w a b u)*(c3_6 y z w a b u))+(((c2_8 y z w a b u)*(c3_5 y z w a b u))+(((c2_9 y z w a b u)*(c3_4 y z w a b u))+(((c2_10 y z w a b u)*(c3_3 y z w a b u))+(((c2_11 y z w a b u)*(c3_2 y z w a b u))+(((c2_12 y z w a b u)*(c3_1 y z w a b u))+(((c2_13 y z w a b u)*(c3_0 y z w a b u))+0))))))))))+((-1)*(c4_13 y z w a b u))) := by
  simp only [innerCertificate,evaluate_add,evaluate_multiply,bind_c0_0,bind_c0_1,bind_c0_2,bind_c0_3,bind_c1_10,bind_c1_11,bind_c1_12,bind_c1_13,bind_c2_10,bind_c2_11,bind_c2_12,bind_c2_13,bind_c2_5,bind_c2_6,bind_c2_7,bind_c2_8,bind_c2_9,bind_c3_0,bind_c3_1,bind_c3_2,bind_c3_3,bind_c3_4,bind_c3_5,bind_c3_6,bind_c3_7,bind_c3_8,bind_c4_13,evaluate,mul_zero,add_zero,zero_add]

end SmallLevelTwentySixSource89Split13
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixSource89Split14
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89
def innerCertificate (z w a b u : ℂ) : List ℂ := add (add (add (multiply ((inner0_0 z w a b u)) ((inner1_14 z w a b u))) (add (multiply ((inner0_1 z w a b u)) ((inner1_13 z w a b u))) (add (multiply ((inner0_2 z w a b u)) ((inner1_12 z w a b u))) (multiply ((inner0_3 z w a b u)) ((inner1_11 z w a b u)))))) (add (multiply ((inner2_6 z w a b u)) ((inner3_8 z w a b u))) (add (multiply ((inner2_7 z w a b u)) ((inner3_7 z w a b u))) (add (multiply ((inner2_8 z w a b u)) ((inner3_6 z w a b u))) (add (multiply ((inner2_9 z w a b u)) ((inner3_5 z w a b u))) (add (multiply ((inner2_10 z w a b u)) ((inner3_4 z w a b u))) (add (multiply ((inner2_11 z w a b u)) ((inner3_3 z w a b u))) (add (multiply ((inner2_12 z w a b u)) ((inner3_2 z w a b u))) (add (multiply ((inner2_13 z w a b u)) ((inner3_1 z w a b u))) (add (multiply ((inner2_14 z w a b u)) ((inner3_0 z w a b u))) ([]))))))))))) (multiply ([(-1)]) ((inner4_14 z w a b u)))
theorem inner_length (z w a b u : ℂ) : (innerCertificate z w a b u).length=9 := by
  norm_num [innerCertificate,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner0_3,inner1_11,inner1_12,inner1_13,inner1_14,inner2_10,inner2_11,inner2_12,inner2_13,inner2_14,inner2_6,inner2_7,inner2_8,inner2_9,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner4_14]
theorem inner_eval (y z w a b u : ℂ) : evaluate y (innerCertificate z w a b u)=(((((c0_0 y z w a b u)*(c1_14 y z w a b u))+(((c0_1 y z w a b u)*(c1_13 y z w a b u))+(((c0_2 y z w a b u)*(c1_12 y z w a b u))+((c0_3 y z w a b u)*(c1_11 y z w a b u)))))+(((c2_6 y z w a b u)*(c3_8 y z w a b u))+(((c2_7 y z w a b u)*(c3_7 y z w a b u))+(((c2_8 y z w a b u)*(c3_6 y z w a b u))+(((c2_9 y z w a b u)*(c3_5 y z w a b u))+(((c2_10 y z w a b u)*(c3_4 y z w a b u))+(((c2_11 y z w a b u)*(c3_3 y z w a b u))+(((c2_12 y z w a b u)*(c3_2 y z w a b u))+(((c2_13 y z w a b u)*(c3_1 y z w a b u))+(((c2_14 y z w a b u)*(c3_0 y z w a b u))+0))))))))))+((-1)*(c4_14 y z w a b u))) := by
  simp only [innerCertificate,evaluate_add,evaluate_multiply,bind_c0_0,bind_c0_1,bind_c0_2,bind_c0_3,bind_c1_11,bind_c1_12,bind_c1_13,bind_c1_14,bind_c2_10,bind_c2_11,bind_c2_12,bind_c2_13,bind_c2_14,bind_c2_6,bind_c2_7,bind_c2_8,bind_c2_9,bind_c3_0,bind_c3_1,bind_c3_2,bind_c3_3,bind_c3_4,bind_c3_5,bind_c3_6,bind_c3_7,bind_c3_8,bind_c4_14,evaluate,mul_zero,add_zero,zero_add]

end SmallLevelTwentySixSource89Split14
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixSource89Split15
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89
def innerCertificate (z w a b u : ℂ) : List ℂ := add (add (add (multiply ((inner0_0 z w a b u)) ((inner1_15 z w a b u))) (add (multiply ((inner0_1 z w a b u)) ((inner1_14 z w a b u))) (add (multiply ((inner0_2 z w a b u)) ((inner1_13 z w a b u))) (multiply ((inner0_3 z w a b u)) ((inner1_12 z w a b u)))))) (add (multiply ((inner2_7 z w a b u)) ((inner3_8 z w a b u))) (add (multiply ((inner2_8 z w a b u)) ((inner3_7 z w a b u))) (add (multiply ((inner2_9 z w a b u)) ((inner3_6 z w a b u))) (add (multiply ((inner2_10 z w a b u)) ((inner3_5 z w a b u))) (add (multiply ((inner2_11 z w a b u)) ((inner3_4 z w a b u))) (add (multiply ((inner2_12 z w a b u)) ((inner3_3 z w a b u))) (add (multiply ((inner2_13 z w a b u)) ((inner3_2 z w a b u))) (add (multiply ((inner2_14 z w a b u)) ((inner3_1 z w a b u))) (add (multiply ((inner2_15 z w a b u)) ((inner3_0 z w a b u))) ([]))))))))))) (multiply ([(-1)]) ((inner4_15 z w a b u)))
theorem inner_length (z w a b u : ℂ) : (innerCertificate z w a b u).length=9 := by
  norm_num [innerCertificate,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner0_3,inner1_12,inner1_13,inner1_14,inner1_15,inner2_10,inner2_11,inner2_12,inner2_13,inner2_14,inner2_15,inner2_7,inner2_8,inner2_9,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner4_15]
theorem inner_eval (y z w a b u : ℂ) : evaluate y (innerCertificate z w a b u)=(((((c0_0 y z w a b u)*(c1_15 y z w a b u))+(((c0_1 y z w a b u)*(c1_14 y z w a b u))+(((c0_2 y z w a b u)*(c1_13 y z w a b u))+((c0_3 y z w a b u)*(c1_12 y z w a b u)))))+(((c2_7 y z w a b u)*(c3_8 y z w a b u))+(((c2_8 y z w a b u)*(c3_7 y z w a b u))+(((c2_9 y z w a b u)*(c3_6 y z w a b u))+(((c2_10 y z w a b u)*(c3_5 y z w a b u))+(((c2_11 y z w a b u)*(c3_4 y z w a b u))+(((c2_12 y z w a b u)*(c3_3 y z w a b u))+(((c2_13 y z w a b u)*(c3_2 y z w a b u))+(((c2_14 y z w a b u)*(c3_1 y z w a b u))+(((c2_15 y z w a b u)*(c3_0 y z w a b u))+0))))))))))+((-1)*(c4_15 y z w a b u))) := by
  simp only [innerCertificate,evaluate_add,evaluate_multiply,bind_c0_0,bind_c0_1,bind_c0_2,bind_c0_3,bind_c1_12,bind_c1_13,bind_c1_14,bind_c1_15,bind_c2_10,bind_c2_11,bind_c2_12,bind_c2_13,bind_c2_14,bind_c2_15,bind_c2_7,bind_c2_8,bind_c2_9,bind_c3_0,bind_c3_1,bind_c3_2,bind_c3_3,bind_c3_4,bind_c3_5,bind_c3_6,bind_c3_7,bind_c3_8,bind_c4_15,evaluate,mul_zero,add_zero,zero_add]

end SmallLevelTwentySixSource89Split15
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixSource89Split16
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89
def innerCertificate (z w a b u : ℂ) : List ℂ := add (add (add (multiply ((inner0_0 z w a b u)) ((inner1_16 z w a b u))) (add (multiply ((inner0_1 z w a b u)) ((inner1_15 z w a b u))) (add (multiply ((inner0_2 z w a b u)) ((inner1_14 z w a b u))) (multiply ((inner0_3 z w a b u)) ((inner1_13 z w a b u)))))) (add (multiply ((inner2_8 z w a b u)) ((inner3_8 z w a b u))) (add (multiply ((inner2_9 z w a b u)) ((inner3_7 z w a b u))) (add (multiply ((inner2_10 z w a b u)) ((inner3_6 z w a b u))) (add (multiply ((inner2_11 z w a b u)) ((inner3_5 z w a b u))) (add (multiply ((inner2_12 z w a b u)) ((inner3_4 z w a b u))) (add (multiply ((inner2_13 z w a b u)) ((inner3_3 z w a b u))) (add (multiply ((inner2_14 z w a b u)) ((inner3_2 z w a b u))) (add (multiply ((inner2_15 z w a b u)) ((inner3_1 z w a b u))) (add (multiply ((inner2_16 z w a b u)) ((inner3_0 z w a b u))) ([]))))))))))) (multiply ([(-1)]) ((inner4_16 z w a b u)))
theorem inner_length (z w a b u : ℂ) : (innerCertificate z w a b u).length=9 := by
  norm_num [innerCertificate,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner0_3,inner1_13,inner1_14,inner1_15,inner1_16,inner2_10,inner2_11,inner2_12,inner2_13,inner2_14,inner2_15,inner2_16,inner2_8,inner2_9,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner4_16]
theorem inner_eval (y z w a b u : ℂ) : evaluate y (innerCertificate z w a b u)=(((((c0_0 y z w a b u)*(c1_16 y z w a b u))+(((c0_1 y z w a b u)*(c1_15 y z w a b u))+(((c0_2 y z w a b u)*(c1_14 y z w a b u))+((c0_3 y z w a b u)*(c1_13 y z w a b u)))))+(((c2_8 y z w a b u)*(c3_8 y z w a b u))+(((c2_9 y z w a b u)*(c3_7 y z w a b u))+(((c2_10 y z w a b u)*(c3_6 y z w a b u))+(((c2_11 y z w a b u)*(c3_5 y z w a b u))+(((c2_12 y z w a b u)*(c3_4 y z w a b u))+(((c2_13 y z w a b u)*(c3_3 y z w a b u))+(((c2_14 y z w a b u)*(c3_2 y z w a b u))+(((c2_15 y z w a b u)*(c3_1 y z w a b u))+(((c2_16 y z w a b u)*(c3_0 y z w a b u))+0))))))))))+((-1)*(c4_16 y z w a b u))) := by
  simp only [innerCertificate,evaluate_add,evaluate_multiply,bind_c0_0,bind_c0_1,bind_c0_2,bind_c0_3,bind_c1_13,bind_c1_14,bind_c1_15,bind_c1_16,bind_c2_10,bind_c2_11,bind_c2_12,bind_c2_13,bind_c2_14,bind_c2_15,bind_c2_16,bind_c2_8,bind_c2_9,bind_c3_0,bind_c3_1,bind_c3_2,bind_c3_3,bind_c3_4,bind_c3_5,bind_c3_6,bind_c3_7,bind_c3_8,bind_c4_16,evaluate,mul_zero,add_zero,zero_add]

end SmallLevelTwentySixSource89Split16
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixSource89Split17
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89
def innerCertificate (z w a b u : ℂ) : List ℂ := add (add (add (multiply ((inner0_0 z w a b u)) ((inner1_17 z w a b u))) (add (multiply ((inner0_1 z w a b u)) ((inner1_16 z w a b u))) (add (multiply ((inner0_2 z w a b u)) ((inner1_15 z w a b u))) (multiply ((inner0_3 z w a b u)) ((inner1_14 z w a b u)))))) (add (multiply ((inner2_9 z w a b u)) ((inner3_8 z w a b u))) (add (multiply ((inner2_10 z w a b u)) ((inner3_7 z w a b u))) (add (multiply ((inner2_11 z w a b u)) ((inner3_6 z w a b u))) (add (multiply ((inner2_12 z w a b u)) ((inner3_5 z w a b u))) (add (multiply ((inner2_13 z w a b u)) ((inner3_4 z w a b u))) (add (multiply ((inner2_14 z w a b u)) ((inner3_3 z w a b u))) (add (multiply ((inner2_15 z w a b u)) ((inner3_2 z w a b u))) (add (multiply ((inner2_16 z w a b u)) ((inner3_1 z w a b u))) (add (multiply ((inner2_17 z w a b u)) ((inner3_0 z w a b u))) ([]))))))))))) (multiply ([(-1)]) ((inner4_17 z w a b u)))
theorem inner_length (z w a b u : ℂ) : (innerCertificate z w a b u).length=9 := by
  norm_num [innerCertificate,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner0_3,inner1_14,inner1_15,inner1_16,inner1_17,inner2_10,inner2_11,inner2_12,inner2_13,inner2_14,inner2_15,inner2_16,inner2_17,inner2_9,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner4_17]
theorem inner_eval (y z w a b u : ℂ) : evaluate y (innerCertificate z w a b u)=(((((c0_0 y z w a b u)*(c1_17 y z w a b u))+(((c0_1 y z w a b u)*(c1_16 y z w a b u))+(((c0_2 y z w a b u)*(c1_15 y z w a b u))+((c0_3 y z w a b u)*(c1_14 y z w a b u)))))+(((c2_9 y z w a b u)*(c3_8 y z w a b u))+(((c2_10 y z w a b u)*(c3_7 y z w a b u))+(((c2_11 y z w a b u)*(c3_6 y z w a b u))+(((c2_12 y z w a b u)*(c3_5 y z w a b u))+(((c2_13 y z w a b u)*(c3_4 y z w a b u))+(((c2_14 y z w a b u)*(c3_3 y z w a b u))+(((c2_15 y z w a b u)*(c3_2 y z w a b u))+(((c2_16 y z w a b u)*(c3_1 y z w a b u))+(((c2_17 y z w a b u)*(c3_0 y z w a b u))+0))))))))))+((-1)*(c4_17 y z w a b u))) := by
  simp only [innerCertificate,evaluate_add,evaluate_multiply,bind_c0_0,bind_c0_1,bind_c0_2,bind_c0_3,bind_c1_14,bind_c1_15,bind_c1_16,bind_c1_17,bind_c2_10,bind_c2_11,bind_c2_12,bind_c2_13,bind_c2_14,bind_c2_15,bind_c2_16,bind_c2_17,bind_c2_9,bind_c3_0,bind_c3_1,bind_c3_2,bind_c3_3,bind_c3_4,bind_c3_5,bind_c3_6,bind_c3_7,bind_c3_8,bind_c4_17,evaluate,mul_zero,add_zero,zero_add]

end SmallLevelTwentySixSource89Split17
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixSource89Split18
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89
def innerCertificate (z w a b u : ℂ) : List ℂ := add (add (add (multiply ((inner0_0 z w a b u)) ((inner1_18 z w a b u))) (add (multiply ((inner0_1 z w a b u)) ((inner1_17 z w a b u))) (add (multiply ((inner0_2 z w a b u)) ((inner1_16 z w a b u))) (multiply ((inner0_3 z w a b u)) ((inner1_15 z w a b u)))))) (add (multiply ((inner2_10 z w a b u)) ((inner3_8 z w a b u))) (add (multiply ((inner2_11 z w a b u)) ((inner3_7 z w a b u))) (add (multiply ((inner2_12 z w a b u)) ((inner3_6 z w a b u))) (add (multiply ((inner2_13 z w a b u)) ((inner3_5 z w a b u))) (add (multiply ((inner2_14 z w a b u)) ((inner3_4 z w a b u))) (add (multiply ((inner2_15 z w a b u)) ((inner3_3 z w a b u))) (add (multiply ((inner2_16 z w a b u)) ((inner3_2 z w a b u))) (add (multiply ((inner2_17 z w a b u)) ((inner3_1 z w a b u))) (add (multiply ((inner2_18 z w a b u)) ((inner3_0 z w a b u))) ([]))))))))))) (multiply ([(-1)]) ((inner4_18 z w a b u)))
theorem inner_length (z w a b u : ℂ) : (innerCertificate z w a b u).length=9 := by
  norm_num [innerCertificate,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner0_3,inner1_15,inner1_16,inner1_17,inner1_18,inner2_10,inner2_11,inner2_12,inner2_13,inner2_14,inner2_15,inner2_16,inner2_17,inner2_18,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner4_18]
theorem inner_eval (y z w a b u : ℂ) : evaluate y (innerCertificate z w a b u)=(((((c0_0 y z w a b u)*(c1_18 y z w a b u))+(((c0_1 y z w a b u)*(c1_17 y z w a b u))+(((c0_2 y z w a b u)*(c1_16 y z w a b u))+((c0_3 y z w a b u)*(c1_15 y z w a b u)))))+(((c2_10 y z w a b u)*(c3_8 y z w a b u))+(((c2_11 y z w a b u)*(c3_7 y z w a b u))+(((c2_12 y z w a b u)*(c3_6 y z w a b u))+(((c2_13 y z w a b u)*(c3_5 y z w a b u))+(((c2_14 y z w a b u)*(c3_4 y z w a b u))+(((c2_15 y z w a b u)*(c3_3 y z w a b u))+(((c2_16 y z w a b u)*(c3_2 y z w a b u))+(((c2_17 y z w a b u)*(c3_1 y z w a b u))+(((c2_18 y z w a b u)*(c3_0 y z w a b u))+0))))))))))+((-1)*(c4_18 y z w a b u))) := by
  simp only [innerCertificate,evaluate_add,evaluate_multiply,bind_c0_0,bind_c0_1,bind_c0_2,bind_c0_3,bind_c1_15,bind_c1_16,bind_c1_17,bind_c1_18,bind_c2_10,bind_c2_11,bind_c2_12,bind_c2_13,bind_c2_14,bind_c2_15,bind_c2_16,bind_c2_17,bind_c2_18,bind_c3_0,bind_c3_1,bind_c3_2,bind_c3_3,bind_c3_4,bind_c3_5,bind_c3_6,bind_c3_7,bind_c3_8,bind_c4_18,evaluate,mul_zero,add_zero,zero_add]

end SmallLevelTwentySixSource89Split18
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixSource89Split19
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89
def innerCertificate (z w a b u : ℂ) : List ℂ := add (add (add (multiply ((inner0_0 z w a b u)) ((inner1_19 z w a b u))) (add (multiply ((inner0_1 z w a b u)) ((inner1_18 z w a b u))) (add (multiply ((inner0_2 z w a b u)) ((inner1_17 z w a b u))) (multiply ((inner0_3 z w a b u)) ((inner1_16 z w a b u)))))) (add (multiply ((inner2_11 z w a b u)) ((inner3_8 z w a b u))) (add (multiply ((inner2_12 z w a b u)) ((inner3_7 z w a b u))) (add (multiply ((inner2_13 z w a b u)) ((inner3_6 z w a b u))) (add (multiply ((inner2_14 z w a b u)) ((inner3_5 z w a b u))) (add (multiply ((inner2_15 z w a b u)) ((inner3_4 z w a b u))) (add (multiply ((inner2_16 z w a b u)) ((inner3_3 z w a b u))) (add (multiply ((inner2_17 z w a b u)) ((inner3_2 z w a b u))) (add (multiply ((inner2_18 z w a b u)) ((inner3_1 z w a b u))) (add (multiply ((inner2_19 z w a b u)) ((inner3_0 z w a b u))) ([]))))))))))) (multiply ([(-1)]) ((inner4_19 z w a b u)))
theorem inner_length (z w a b u : ℂ) : (innerCertificate z w a b u).length=9 := by
  norm_num [innerCertificate,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner0_3,inner1_16,inner1_17,inner1_18,inner1_19,inner2_11,inner2_12,inner2_13,inner2_14,inner2_15,inner2_16,inner2_17,inner2_18,inner2_19,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner4_19]
theorem inner_eval (y z w a b u : ℂ) : evaluate y (innerCertificate z w a b u)=(((((c0_0 y z w a b u)*(c1_19 y z w a b u))+(((c0_1 y z w a b u)*(c1_18 y z w a b u))+(((c0_2 y z w a b u)*(c1_17 y z w a b u))+((c0_3 y z w a b u)*(c1_16 y z w a b u)))))+(((c2_11 y z w a b u)*(c3_8 y z w a b u))+(((c2_12 y z w a b u)*(c3_7 y z w a b u))+(((c2_13 y z w a b u)*(c3_6 y z w a b u))+(((c2_14 y z w a b u)*(c3_5 y z w a b u))+(((c2_15 y z w a b u)*(c3_4 y z w a b u))+(((c2_16 y z w a b u)*(c3_3 y z w a b u))+(((c2_17 y z w a b u)*(c3_2 y z w a b u))+(((c2_18 y z w a b u)*(c3_1 y z w a b u))+(((c2_19 y z w a b u)*(c3_0 y z w a b u))+0))))))))))+((-1)*(c4_19 y z w a b u))) := by
  simp only [innerCertificate,evaluate_add,evaluate_multiply,bind_c0_0,bind_c0_1,bind_c0_2,bind_c0_3,bind_c1_16,bind_c1_17,bind_c1_18,bind_c1_19,bind_c2_11,bind_c2_12,bind_c2_13,bind_c2_14,bind_c2_15,bind_c2_16,bind_c2_17,bind_c2_18,bind_c2_19,bind_c3_0,bind_c3_1,bind_c3_2,bind_c3_3,bind_c3_4,bind_c3_5,bind_c3_6,bind_c3_7,bind_c3_8,bind_c4_19,evaluate,mul_zero,add_zero,zero_add]

end SmallLevelTwentySixSource89Split19
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixSource89Split20
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89
def innerCertificate (z w a b u : ℂ) : List ℂ := add (add (add (multiply ((inner0_0 z w a b u)) ((inner1_20 z w a b u))) (add (multiply ((inner0_1 z w a b u)) ((inner1_19 z w a b u))) (add (multiply ((inner0_2 z w a b u)) ((inner1_18 z w a b u))) (multiply ((inner0_3 z w a b u)) ((inner1_17 z w a b u)))))) (add (multiply ((inner2_12 z w a b u)) ((inner3_8 z w a b u))) (add (multiply ((inner2_13 z w a b u)) ((inner3_7 z w a b u))) (add (multiply ((inner2_14 z w a b u)) ((inner3_6 z w a b u))) (add (multiply ((inner2_15 z w a b u)) ((inner3_5 z w a b u))) (add (multiply ((inner2_16 z w a b u)) ((inner3_4 z w a b u))) (add (multiply ((inner2_17 z w a b u)) ((inner3_3 z w a b u))) (add (multiply ((inner2_18 z w a b u)) ((inner3_2 z w a b u))) (add (multiply ((inner2_19 z w a b u)) ((inner3_1 z w a b u))) (add (multiply ((inner2_20 z w a b u)) ((inner3_0 z w a b u))) ([]))))))))))) (multiply ([(-1)]) ((inner4_20 z w a b u)))
theorem inner_length (z w a b u : ℂ) : (innerCertificate z w a b u).length=8 := by
  norm_num [innerCertificate,add,multiply,scale,inner0_0,inner0_1,inner0_2,inner0_3,inner1_17,inner1_18,inner1_19,inner1_20,inner2_12,inner2_13,inner2_14,inner2_15,inner2_16,inner2_17,inner2_18,inner2_19,inner2_20,inner3_0,inner3_1,inner3_2,inner3_3,inner3_4,inner3_5,inner3_6,inner3_7,inner3_8,inner4_20]
theorem inner_eval (y z w a b u : ℂ) : evaluate y (innerCertificate z w a b u)=(((((c0_0 y z w a b u)*(c1_20 y z w a b u))+(((c0_1 y z w a b u)*(c1_19 y z w a b u))+(((c0_2 y z w a b u)*(c1_18 y z w a b u))+((c0_3 y z w a b u)*(c1_17 y z w a b u)))))+(((c2_12 y z w a b u)*(c3_8 y z w a b u))+(((c2_13 y z w a b u)*(c3_7 y z w a b u))+(((c2_14 y z w a b u)*(c3_6 y z w a b u))+(((c2_15 y z w a b u)*(c3_5 y z w a b u))+(((c2_16 y z w a b u)*(c3_4 y z w a b u))+(((c2_17 y z w a b u)*(c3_3 y z w a b u))+(((c2_18 y z w a b u)*(c3_2 y z w a b u))+(((c2_19 y z w a b u)*(c3_1 y z w a b u))+(((c2_20 y z w a b u)*(c3_0 y z w a b u))+0))))))))))+((-1)*(c4_20 y z w a b u))) := by
  simp only [innerCertificate,evaluate_add,evaluate_multiply,bind_c0_0,bind_c0_1,bind_c0_2,bind_c0_3,bind_c1_17,bind_c1_18,bind_c1_19,bind_c1_20,bind_c2_12,bind_c2_13,bind_c2_14,bind_c2_15,bind_c2_16,bind_c2_17,bind_c2_18,bind_c2_19,bind_c2_20,bind_c3_0,bind_c3_1,bind_c3_2,bind_c3_3,bind_c3_4,bind_c3_5,bind_c3_6,bind_c3_7,bind_c3_8,bind_c4_20,evaluate,mul_zero,add_zero,zero_add]

end SmallLevelTwentySixSource89Split20
end

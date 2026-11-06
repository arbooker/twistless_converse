module
public import SmallLevelTwentySixMMPPariSyzygyIndexColumnIndexDataSeriesV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariSyzygy6Column0
open SmallLevelPolynomialCoefficientCertificate

theorem coefficient_0 (y z w a b : ℂ) : (certificate y z w a b)[0]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_0 y z w a b))+0)+((-1)*(((c2_0 y z w a b)*(c3_0 y z w a b))+0)))+((-1)*(((c4_0 y z w a b)*(c5_0 y z w a b))+0)))+((-1)*(((c6_0 y z w a b)*(c7_0 y z w a b))+0)))+((-1)*(((c8_0 y z w a b)*(c9_0 y z w a b))+0)))+((-1)*(c10_0 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c10_0,c1_0,c2_0,c3_0,c4_0,c5_0,c6_0,c7_0,c8_0,c9_0]
  ring
#print axioms coefficient_0
theorem coefficient_1 (y z w a b : ℂ) : (certificate y z w a b)[1]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_1 y z w a b))+(((c0_1 y z w a b)*(c1_0 y z w a b))+0))+((-1)*(((c2_0 y z w a b)*(c3_1 y z w a b))+(((c2_1 y z w a b)*(c3_0 y z w a b))+0))))+((-1)*(((c4_0 y z w a b)*(c5_1 y z w a b))+(((c4_1 y z w a b)*(c5_0 y z w a b))+0))))+((-1)*(((c6_0 y z w a b)*(c7_1 y z w a b))+(((c6_1 y z w a b)*(c7_0 y z w a b))+0))))+((-1)*(((c8_0 y z w a b)*(c9_1 y z w a b))+(((c8_1 y z w a b)*(c9_0 y z w a b))+0))))+((-1)*(c10_1 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c10_1,c1_0,c1_1,c2_0,c2_1,c3_0,c3_1,c4_0,c4_1,c5_0,c5_1,c6_0,c6_1,c7_0,c7_1,c8_0,c8_1,c9_0,c9_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (y z w a b : ℂ) : (certificate y z w a b)[2]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_2 y z w a b))+(((c0_1 y z w a b)*(c1_1 y z w a b))+(((c0_2 y z w a b)*(c1_0 y z w a b))+0)))+((-1)*(((c2_0 y z w a b)*(c3_2 y z w a b))+(((c2_1 y z w a b)*(c3_1 y z w a b))+(((c2_2 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_0 y z w a b)*(c5_2 y z w a b))+(((c4_1 y z w a b)*(c5_1 y z w a b))+(((c4_2 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_0 y z w a b)*(c7_2 y z w a b))+(((c6_1 y z w a b)*(c7_1 y z w a b))+(((c6_2 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_2 y z w a b))+(((c8_1 y z w a b)*(c9_1 y z w a b))+(((c8_2 y z w a b)*(c9_0 y z w a b))+0)))))+((-1)*(c10_2 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c10_2,c1_0,c1_1,c1_2,c2_0,c2_1,c2_2,c3_0,c3_1,c3_2,c4_0,c4_1,c4_2,c5_0,c5_1,c5_2,c6_0,c6_1,c6_2,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_2
theorem coefficient_3 (y z w a b : ℂ) : (certificate y z w a b)[3]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_3 y z w a b))+(((c0_1 y z w a b)*(c1_2 y z w a b))+(((c0_2 y z w a b)*(c1_1 y z w a b))+(((c0_3 y z w a b)*(c1_0 y z w a b))+0))))+((-1)*(((c2_0 y z w a b)*(c3_3 y z w a b))+(((c2_1 y z w a b)*(c3_2 y z w a b))+(((c2_2 y z w a b)*(c3_1 y z w a b))+(((c2_3 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_0 y z w a b)*(c5_3 y z w a b))+(((c4_1 y z w a b)*(c5_2 y z w a b))+(((c4_2 y z w a b)*(c5_1 y z w a b))+(((c4_3 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_0 y z w a b)*(c7_3 y z w a b))+(((c6_1 y z w a b)*(c7_2 y z w a b))+(((c6_2 y z w a b)*(c7_1 y z w a b))+(((c6_3 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_0 y z w a b)*(c9_3 y z w a b))+(((c8_1 y z w a b)*(c9_2 y z w a b))+(((c8_2 y z w a b)*(c9_1 y z w a b))+(((c8_3 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_3 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c10_3,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c3_0,c3_1,c3_2,c3_3,c4_0,c4_1,c4_2,c4_3,c5_0,c5_1,c5_2,c5_3,c6_0,c6_1,c6_2,c6_3,c7_0,c7_1,c7_2,c7_3,c8_0,c8_1,c8_2,c8_3,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (y z w a b : ℂ) : (certificate y z w a b)[4]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_4 y z w a b))+(((c0_1 y z w a b)*(c1_3 y z w a b))+(((c0_2 y z w a b)*(c1_2 y z w a b))+(((c0_3 y z w a b)*(c1_1 y z w a b))+(((c0_4 y z w a b)*(c1_0 y z w a b))+0)))))+((-1)*(((c2_1 y z w a b)*(c3_3 y z w a b))+(((c2_2 y z w a b)*(c3_2 y z w a b))+(((c2_3 y z w a b)*(c3_1 y z w a b))+(((c2_4 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_1 y z w a b)*(c5_3 y z w a b))+(((c4_2 y z w a b)*(c5_2 y z w a b))+(((c4_3 y z w a b)*(c5_1 y z w a b))+(((c4_4 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_1 y z w a b)*(c7_3 y z w a b))+(((c6_2 y z w a b)*(c7_2 y z w a b))+(((c6_3 y z w a b)*(c7_1 y z w a b))+(((c6_4 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_0 y z w a b)*(c9_4 y z w a b))+(((c8_1 y z w a b)*(c9_3 y z w a b))+(((c8_2 y z w a b)*(c9_2 y z w a b))+(((c8_3 y z w a b)*(c9_1 y z w a b))+(((c8_4 y z w a b)*(c9_0 y z w a b))+0)))))))+((-1)*(c10_4 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c10_4,c1_0,c1_1,c1_2,c1_3,c1_4,c2_1,c2_2,c2_3,c2_4,c3_0,c3_1,c3_2,c3_3,c4_1,c4_2,c4_3,c4_4,c5_0,c5_1,c5_2,c5_3,c6_1,c6_2,c6_3,c6_4,c7_0,c7_1,c7_2,c7_3,c8_0,c8_1,c8_2,c8_3,c8_4,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_4
theorem coefficient_5 (y z w a b : ℂ) : (certificate y z w a b)[5]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_5 y z w a b))+(((c0_1 y z w a b)*(c1_4 y z w a b))+(((c0_2 y z w a b)*(c1_3 y z w a b))+(((c0_3 y z w a b)*(c1_2 y z w a b))+(((c0_4 y z w a b)*(c1_1 y z w a b))+(((c0_5 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*(((c2_2 y z w a b)*(c3_3 y z w a b))+(((c2_3 y z w a b)*(c3_2 y z w a b))+(((c2_4 y z w a b)*(c3_1 y z w a b))+(((c2_5 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_2 y z w a b)*(c5_3 y z w a b))+(((c4_3 y z w a b)*(c5_2 y z w a b))+(((c4_4 y z w a b)*(c5_1 y z w a b))+(((c4_5 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_2 y z w a b)*(c7_3 y z w a b))+(((c6_3 y z w a b)*(c7_2 y z w a b))+(((c6_4 y z w a b)*(c7_1 y z w a b))+(((c6_5 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_1 y z w a b)*(c9_4 y z w a b))+(((c8_2 y z w a b)*(c9_3 y z w a b))+(((c8_3 y z w a b)*(c9_2 y z w a b))+(((c8_4 y z w a b)*(c9_1 y z w a b))+(((c8_5 y z w a b)*(c9_0 y z w a b))+0)))))))+((-1)*(c10_5 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c10_5,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_2,c2_3,c2_4,c2_5,c3_0,c3_1,c3_2,c3_3,c4_2,c4_3,c4_4,c4_5,c5_0,c5_1,c5_2,c5_3,c6_2,c6_3,c6_4,c6_5,c7_0,c7_1,c7_2,c7_3,c8_1,c8_2,c8_3,c8_4,c8_5,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_5

theorem coefficient_6 (y z w a b : ℂ) : (certificate y z w a b)[6]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_6 y z w a b))+(((c0_1 y z w a b)*(c1_5 y z w a b))+(((c0_2 y z w a b)*(c1_4 y z w a b))+(((c0_3 y z w a b)*(c1_3 y z w a b))+(((c0_4 y z w a b)*(c1_2 y z w a b))+(((c0_5 y z w a b)*(c1_1 y z w a b))+(((c0_6 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*(((c2_3 y z w a b)*(c3_3 y z w a b))+(((c2_4 y z w a b)*(c3_2 y z w a b))+(((c2_5 y z w a b)*(c3_1 y z w a b))+(((c2_6 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_3 y z w a b)*(c5_3 y z w a b))+(((c4_4 y z w a b)*(c5_2 y z w a b))+(((c4_5 y z w a b)*(c5_1 y z w a b))+(((c4_6 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_3 y z w a b)*(c7_3 y z w a b))+(((c6_4 y z w a b)*(c7_2 y z w a b))+(((c6_5 y z w a b)*(c7_1 y z w a b))+(((c6_6 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_2 y z w a b)*(c9_4 y z w a b))+(((c8_3 y z w a b)*(c9_3 y z w a b))+(((c8_4 y z w a b)*(c9_2 y z w a b))+(((c8_5 y z w a b)*(c9_1 y z w a b))+(((c8_6 y z w a b)*(c9_0 y z w a b))+0)))))))+((-1)*(c10_6 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c10_6,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_3,c2_4,c2_5,c2_6,c3_0,c3_1,c3_2,c3_3,c4_3,c4_4,c4_5,c4_6,c5_0,c5_1,c5_2,c5_3,c6_3,c6_4,c6_5,c6_6,c7_0,c7_1,c7_2,c7_3,c8_2,c8_3,c8_4,c8_5,c8_6,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_6
theorem coefficient_7 (y z w a b : ℂ) : (certificate y z w a b)[7]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_7 y z w a b))+(((c0_1 y z w a b)*(c1_6 y z w a b))+(((c0_2 y z w a b)*(c1_5 y z w a b))+(((c0_3 y z w a b)*(c1_4 y z w a b))+(((c0_4 y z w a b)*(c1_3 y z w a b))+(((c0_5 y z w a b)*(c1_2 y z w a b))+(((c0_6 y z w a b)*(c1_1 y z w a b))+(((c0_7 y z w a b)*(c1_0 y z w a b))+0))))))))+((-1)*(((c2_4 y z w a b)*(c3_3 y z w a b))+(((c2_5 y z w a b)*(c3_2 y z w a b))+(((c2_6 y z w a b)*(c3_1 y z w a b))+(((c2_7 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_4 y z w a b)*(c5_3 y z w a b))+(((c4_5 y z w a b)*(c5_2 y z w a b))+(((c4_6 y z w a b)*(c5_1 y z w a b))+(((c4_7 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_4 y z w a b)*(c7_3 y z w a b))+(((c6_5 y z w a b)*(c7_2 y z w a b))+(((c6_6 y z w a b)*(c7_1 y z w a b))+(((c6_7 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_3 y z w a b)*(c9_4 y z w a b))+(((c8_4 y z w a b)*(c9_3 y z w a b))+(((c8_5 y z w a b)*(c9_2 y z w a b))+(((c8_6 y z w a b)*(c9_1 y z w a b))+(((c8_7 y z w a b)*(c9_0 y z w a b))+0)))))))+((-1)*(c10_7 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c10_7,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c2_4,c2_5,c2_6,c2_7,c3_0,c3_1,c3_2,c3_3,c4_4,c4_5,c4_6,c4_7,c5_0,c5_1,c5_2,c5_3,c6_4,c6_5,c6_6,c6_7,c7_0,c7_1,c7_2,c7_3,c8_3,c8_4,c8_5,c8_6,c8_7,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_7

theorem coefficient_8 (y z w a b : ℂ) : (certificate y z w a b)[8]?=some 0 := by
  change some (((((((((c0_1 y z w a b)*(c1_7 y z w a b))+(((c0_2 y z w a b)*(c1_6 y z w a b))+(((c0_3 y z w a b)*(c1_5 y z w a b))+(((c0_4 y z w a b)*(c1_4 y z w a b))+(((c0_5 y z w a b)*(c1_3 y z w a b))+(((c0_6 y z w a b)*(c1_2 y z w a b))+(((c0_7 y z w a b)*(c1_1 y z w a b))+(((c0_8 y z w a b)*(c1_0 y z w a b))+0))))))))+((-1)*(((c2_5 y z w a b)*(c3_3 y z w a b))+(((c2_6 y z w a b)*(c3_2 y z w a b))+(((c2_7 y z w a b)*(c3_1 y z w a b))+(((c2_8 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_5 y z w a b)*(c5_3 y z w a b))+(((c4_6 y z w a b)*(c5_2 y z w a b))+(((c4_7 y z w a b)*(c5_1 y z w a b))+(((c4_8 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_5 y z w a b)*(c7_3 y z w a b))+(((c6_6 y z w a b)*(c7_2 y z w a b))+(((c6_7 y z w a b)*(c7_1 y z w a b))+(((c6_8 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_4 y z w a b)*(c9_4 y z w a b))+(((c8_5 y z w a b)*(c9_3 y z w a b))+(((c8_6 y z w a b)*(c9_2 y z w a b))+(((c8_7 y z w a b)*(c9_1 y z w a b))+(((c8_8 y z w a b)*(c9_0 y z w a b))+0)))))))+((-1)*(c10_8 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c10_8,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c2_5,c2_6,c2_7,c2_8,c3_0,c3_1,c3_2,c3_3,c4_5,c4_6,c4_7,c4_8,c5_0,c5_1,c5_2,c5_3,c6_5,c6_6,c6_7,c6_8,c7_0,c7_1,c7_2,c7_3,c8_4,c8_5,c8_6,c8_7,c8_8,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_8
theorem coefficient_9 (y z w a b : ℂ) : (certificate y z w a b)[9]?=some 0 := by
  change some (((((((((c0_2 y z w a b)*(c1_7 y z w a b))+(((c0_3 y z w a b)*(c1_6 y z w a b))+(((c0_4 y z w a b)*(c1_5 y z w a b))+(((c0_5 y z w a b)*(c1_4 y z w a b))+(((c0_6 y z w a b)*(c1_3 y z w a b))+(((c0_7 y z w a b)*(c1_2 y z w a b))+((c0_8 y z w a b)*(c1_1 y z w a b))))))))+((-1)*(((c2_6 y z w a b)*(c3_3 y z w a b))+(((c2_7 y z w a b)*(c3_2 y z w a b))+(((c2_8 y z w a b)*(c3_1 y z w a b))+(((c2_9 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_6 y z w a b)*(c5_3 y z w a b))+(((c4_7 y z w a b)*(c5_2 y z w a b))+(((c4_8 y z w a b)*(c5_1 y z w a b))+(((c4_9 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_6 y z w a b)*(c7_3 y z w a b))+(((c6_7 y z w a b)*(c7_2 y z w a b))+(((c6_8 y z w a b)*(c7_1 y z w a b))+(((c6_9 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_5 y z w a b)*(c9_4 y z w a b))+(((c8_6 y z w a b)*(c9_3 y z w a b))+(((c8_7 y z w a b)*(c9_2 y z w a b))+(((c8_8 y z w a b)*(c9_1 y z w a b))+(((c8_9 y z w a b)*(c9_0 y z w a b))+0)))))))+((-1)*(c10_9 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c10_9,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_2,c3_3,c4_6,c4_7,c4_8,c4_9,c5_0,c5_1,c5_2,c5_3,c6_6,c6_7,c6_8,c6_9,c7_0,c7_1,c7_2,c7_3,c8_5,c8_6,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_9

theorem coefficient_10 (y z w a b : ℂ) : (certificate y z w a b)[10]?=some 0 := by
  change some (((((((((c0_3 y z w a b)*(c1_7 y z w a b))+(((c0_4 y z w a b)*(c1_6 y z w a b))+(((c0_5 y z w a b)*(c1_5 y z w a b))+(((c0_6 y z w a b)*(c1_4 y z w a b))+(((c0_7 y z w a b)*(c1_3 y z w a b))+((c0_8 y z w a b)*(c1_2 y z w a b)))))))+((-1)*(((c2_7 y z w a b)*(c3_3 y z w a b))+(((c2_8 y z w a b)*(c3_2 y z w a b))+(((c2_9 y z w a b)*(c3_1 y z w a b))+(((c2_10 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_7 y z w a b)*(c5_3 y z w a b))+(((c4_8 y z w a b)*(c5_2 y z w a b))+(((c4_9 y z w a b)*(c5_1 y z w a b))+(((c4_10 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_7 y z w a b)*(c7_3 y z w a b))+(((c6_8 y z w a b)*(c7_2 y z w a b))+((c6_9 y z w a b)*(c7_1 y z w a b))))))+((-1)*(((c8_6 y z w a b)*(c9_4 y z w a b))+(((c8_7 y z w a b)*(c9_3 y z w a b))+(((c8_8 y z w a b)*(c9_2 y z w a b))+(((c8_9 y z w a b)*(c9_1 y z w a b))+(((c8_10 y z w a b)*(c9_0 y z w a b))+0)))))))+((-1)*(c10_10 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c10_10,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c2_10,c2_7,c2_8,c2_9,c3_0,c3_1,c3_2,c3_3,c4_10,c4_7,c4_8,c4_9,c5_0,c5_1,c5_2,c5_3,c6_7,c6_8,c6_9,c7_1,c7_2,c7_3,c8_10,c8_6,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_10
theorem coefficient_11 (y z w a b : ℂ) : (certificate y z w a b)[11]?=some 0 := by
  change some (((((((((c0_4 y z w a b)*(c1_7 y z w a b))+(((c0_5 y z w a b)*(c1_6 y z w a b))+(((c0_6 y z w a b)*(c1_5 y z w a b))+(((c0_7 y z w a b)*(c1_4 y z w a b))+((c0_8 y z w a b)*(c1_3 y z w a b))))))+((-1)*(((c2_8 y z w a b)*(c3_3 y z w a b))+(((c2_9 y z w a b)*(c3_2 y z w a b))+(((c2_10 y z w a b)*(c3_1 y z w a b))+(((c2_11 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_8 y z w a b)*(c5_3 y z w a b))+(((c4_9 y z w a b)*(c5_2 y z w a b))+(((c4_10 y z w a b)*(c5_1 y z w a b))+(((c4_11 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_8 y z w a b)*(c7_3 y z w a b))+((c6_9 y z w a b)*(c7_2 y z w a b)))))+((-1)*(((c8_7 y z w a b)*(c9_4 y z w a b))+(((c8_8 y z w a b)*(c9_3 y z w a b))+(((c8_9 y z w a b)*(c9_2 y z w a b))+((c8_10 y z w a b)*(c9_1 y z w a b)))))))+((-1)*(c10_11 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_4,c0_5,c0_6,c0_7,c0_8,c10_11,c1_3,c1_4,c1_5,c1_6,c1_7,c2_10,c2_11,c2_8,c2_9,c3_0,c3_1,c3_2,c3_3,c4_10,c4_11,c4_8,c4_9,c5_0,c5_1,c5_2,c5_3,c6_8,c6_9,c7_2,c7_3,c8_10,c8_7,c8_8,c8_9,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_11

theorem coefficient_12 (y z w a b : ℂ) : (certificate y z w a b)[12]?=some 0 := by
  change some (((((((((c0_5 y z w a b)*(c1_7 y z w a b))+(((c0_6 y z w a b)*(c1_6 y z w a b))+(((c0_7 y z w a b)*(c1_5 y z w a b))+((c0_8 y z w a b)*(c1_4 y z w a b)))))+((-1)*(((c2_9 y z w a b)*(c3_3 y z w a b))+(((c2_10 y z w a b)*(c3_2 y z w a b))+((c2_11 y z w a b)*(c3_1 y z w a b))))))+((-1)*(((c4_9 y z w a b)*(c5_3 y z w a b))+(((c4_10 y z w a b)*(c5_2 y z w a b))+(((c4_11 y z w a b)*(c5_1 y z w a b))+(((c4_12 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*((c6_9 y z w a b)*(c7_3 y z w a b))))+((-1)*(((c8_8 y z w a b)*(c9_4 y z w a b))+(((c8_9 y z w a b)*(c9_3 y z w a b))+((c8_10 y z w a b)*(c9_2 y z w a b))))))+((-1)*(c10_12 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_5,c0_6,c0_7,c0_8,c10_12,c1_4,c1_5,c1_6,c1_7,c2_10,c2_11,c2_9,c3_1,c3_2,c3_3,c4_10,c4_11,c4_12,c4_9,c5_0,c5_1,c5_2,c5_3,c6_9,c7_3,c8_10,c8_8,c8_9,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_12
theorem coefficient_13 (y z w a b : ℂ) : (certificate y z w a b)[13]?=some 0 := by
  change some ((((((((c0_6 y z w a b)*(c1_7 y z w a b))+(((c0_7 y z w a b)*(c1_6 y z w a b))+((c0_8 y z w a b)*(c1_5 y z w a b))))+((-1)*(((c2_10 y z w a b)*(c3_3 y z w a b))+((c2_11 y z w a b)*(c3_2 y z w a b)))))+((-1)*(((c4_10 y z w a b)*(c5_3 y z w a b))+(((c4_11 y z w a b)*(c5_2 y z w a b))+((c4_12 y z w a b)*(c5_1 y z w a b))))))+((-1)*(((c8_9 y z w a b)*(c9_4 y z w a b))+((c8_10 y z w a b)*(c9_3 y z w a b)))))+((-1)*(c10_13 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_6,c0_7,c0_8,c10_13,c1_5,c1_6,c1_7,c2_10,c2_11,c3_2,c3_3,c4_10,c4_11,c4_12,c5_1,c5_2,c5_3,c8_10,c8_9,c9_3,c9_4]
  ring
#print axioms coefficient_13

theorem coefficient_14 (y z w a b : ℂ) : (certificate y z w a b)[14]?=some 0 := by
  change some ((((((((c0_7 y z w a b)*(c1_7 y z w a b))+((c0_8 y z w a b)*(c1_6 y z w a b)))+((-1)*((c2_11 y z w a b)*(c3_3 y z w a b))))+((-1)*(((c4_11 y z w a b)*(c5_3 y z w a b))+((c4_12 y z w a b)*(c5_2 y z w a b)))))+((-1)*((c8_10 y z w a b)*(c9_4 y z w a b))))+((-1)*(c10_14 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_7,c0_8,c10_14,c1_6,c1_7,c2_11,c3_3,c4_11,c4_12,c5_2,c5_3,c8_10,c9_4]
  ring
#print axioms coefficient_14
theorem coefficient_15 (y z w a b : ℂ) : (certificate y z w a b)[15]?=some 0 := by
  change some (((((c0_8 y z w a b)*(c1_7 y z w a b))+((-1)*((c4_12 y z w a b)*(c5_3 y z w a b))))+((-1)*(c10_15 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_8,c10_15,c1_7,c4_12,c5_3]
  ring
#print axioms coefficient_15

end SmallLevelTwentySixMMPPariSyzygy6Column0
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariSyzygy6Column1
open SmallLevelPolynomialCoefficientCertificate

theorem coefficient_0 (y z w a b : ℂ) : (certificate y z w a b)[0]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_0 y z w a b))+0)+((-1)*(((c2_0 y z w a b)*(c3_0 y z w a b))+0)))+((-1)*(((c4_0 y z w a b)*(c5_0 y z w a b))+0)))+((-1)*(((c6_0 y z w a b)*(c7_0 y z w a b))+0)))+((-1)*(((c8_0 y z w a b)*(c9_0 y z w a b))+0)))+((-1)*(c10_0 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c10_0,c1_0,c2_0,c3_0,c4_0,c5_0,c6_0,c7_0,c8_0,c9_0]
  ring
#print axioms coefficient_0
theorem coefficient_1 (y z w a b : ℂ) : (certificate y z w a b)[1]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_1 y z w a b))+(((c0_1 y z w a b)*(c1_0 y z w a b))+0))+((-1)*(((c2_0 y z w a b)*(c3_1 y z w a b))+(((c2_1 y z w a b)*(c3_0 y z w a b))+0))))+((-1)*(((c4_0 y z w a b)*(c5_1 y z w a b))+(((c4_1 y z w a b)*(c5_0 y z w a b))+0))))+((-1)*(((c6_0 y z w a b)*(c7_1 y z w a b))+(((c6_1 y z w a b)*(c7_0 y z w a b))+0))))+((-1)*(((c8_0 y z w a b)*(c9_1 y z w a b))+(((c8_1 y z w a b)*(c9_0 y z w a b))+0))))+((-1)*(c10_1 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c10_1,c1_0,c1_1,c2_0,c2_1,c3_0,c3_1,c4_0,c4_1,c5_0,c5_1,c6_0,c6_1,c7_0,c7_1,c8_0,c8_1,c9_0,c9_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (y z w a b : ℂ) : (certificate y z w a b)[2]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_2 y z w a b))+(((c0_1 y z w a b)*(c1_1 y z w a b))+(((c0_2 y z w a b)*(c1_0 y z w a b))+0)))+((-1)*(((c2_0 y z w a b)*(c3_2 y z w a b))+(((c2_1 y z w a b)*(c3_1 y z w a b))+(((c2_2 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_0 y z w a b)*(c5_2 y z w a b))+(((c4_1 y z w a b)*(c5_1 y z w a b))+(((c4_2 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_0 y z w a b)*(c7_2 y z w a b))+(((c6_1 y z w a b)*(c7_1 y z w a b))+(((c6_2 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_2 y z w a b))+(((c8_1 y z w a b)*(c9_1 y z w a b))+(((c8_2 y z w a b)*(c9_0 y z w a b))+0)))))+((-1)*(c10_2 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c10_2,c1_0,c1_1,c1_2,c2_0,c2_1,c2_2,c3_0,c3_1,c3_2,c4_0,c4_1,c4_2,c5_0,c5_1,c5_2,c6_0,c6_1,c6_2,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_2
theorem coefficient_3 (y z w a b : ℂ) : (certificate y z w a b)[3]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_3 y z w a b))+(((c0_1 y z w a b)*(c1_2 y z w a b))+(((c0_2 y z w a b)*(c1_1 y z w a b))+(((c0_3 y z w a b)*(c1_0 y z w a b))+0))))+((-1)*(((c2_1 y z w a b)*(c3_2 y z w a b))+(((c2_2 y z w a b)*(c3_1 y z w a b))+(((c2_3 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_1 y z w a b)*(c5_2 y z w a b))+(((c4_2 y z w a b)*(c5_1 y z w a b))+(((c4_3 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_1 y z w a b)*(c7_2 y z w a b))+(((c6_2 y z w a b)*(c7_1 y z w a b))+(((c6_3 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_3 y z w a b))+(((c8_1 y z w a b)*(c9_2 y z w a b))+(((c8_2 y z w a b)*(c9_1 y z w a b))+(((c8_3 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_3 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c10_3,c1_0,c1_1,c1_2,c1_3,c2_1,c2_2,c2_3,c3_0,c3_1,c3_2,c4_1,c4_2,c4_3,c5_0,c5_1,c5_2,c6_1,c6_2,c6_3,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c8_3,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (y z w a b : ℂ) : (certificate y z w a b)[4]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_4 y z w a b))+(((c0_1 y z w a b)*(c1_3 y z w a b))+(((c0_2 y z w a b)*(c1_2 y z w a b))+(((c0_3 y z w a b)*(c1_1 y z w a b))+(((c0_4 y z w a b)*(c1_0 y z w a b))+0)))))+((-1)*(((c2_2 y z w a b)*(c3_2 y z w a b))+(((c2_3 y z w a b)*(c3_1 y z w a b))+(((c2_4 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_2 y z w a b)*(c5_2 y z w a b))+(((c4_3 y z w a b)*(c5_1 y z w a b))+(((c4_4 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_2 y z w a b)*(c7_2 y z w a b))+(((c6_3 y z w a b)*(c7_1 y z w a b))+(((c6_4 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_1 y z w a b)*(c9_3 y z w a b))+(((c8_2 y z w a b)*(c9_2 y z w a b))+(((c8_3 y z w a b)*(c9_1 y z w a b))+(((c8_4 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_4 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c10_4,c1_0,c1_1,c1_2,c1_3,c1_4,c2_2,c2_3,c2_4,c3_0,c3_1,c3_2,c4_2,c4_3,c4_4,c5_0,c5_1,c5_2,c6_2,c6_3,c6_4,c7_0,c7_1,c7_2,c8_1,c8_2,c8_3,c8_4,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_4
theorem coefficient_5 (y z w a b : ℂ) : (certificate y z w a b)[5]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_5 y z w a b))+(((c0_1 y z w a b)*(c1_4 y z w a b))+(((c0_2 y z w a b)*(c1_3 y z w a b))+(((c0_3 y z w a b)*(c1_2 y z w a b))+(((c0_4 y z w a b)*(c1_1 y z w a b))+(((c0_5 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*(((c2_3 y z w a b)*(c3_2 y z w a b))+(((c2_4 y z w a b)*(c3_1 y z w a b))+(((c2_5 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_3 y z w a b)*(c5_2 y z w a b))+(((c4_4 y z w a b)*(c5_1 y z w a b))+(((c4_5 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_3 y z w a b)*(c7_2 y z w a b))+(((c6_4 y z w a b)*(c7_1 y z w a b))+(((c6_5 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_2 y z w a b)*(c9_3 y z w a b))+(((c8_3 y z w a b)*(c9_2 y z w a b))+(((c8_4 y z w a b)*(c9_1 y z w a b))+(((c8_5 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_5 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c10_5,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_3,c2_4,c2_5,c3_0,c3_1,c3_2,c4_3,c4_4,c4_5,c5_0,c5_1,c5_2,c6_3,c6_4,c6_5,c7_0,c7_1,c7_2,c8_2,c8_3,c8_4,c8_5,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_5

theorem coefficient_6 (y z w a b : ℂ) : (certificate y z w a b)[6]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_6 y z w a b))+(((c0_1 y z w a b)*(c1_5 y z w a b))+(((c0_2 y z w a b)*(c1_4 y z w a b))+(((c0_3 y z w a b)*(c1_3 y z w a b))+(((c0_4 y z w a b)*(c1_2 y z w a b))+(((c0_5 y z w a b)*(c1_1 y z w a b))+(((c0_6 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*(((c2_4 y z w a b)*(c3_2 y z w a b))+(((c2_5 y z w a b)*(c3_1 y z w a b))+(((c2_6 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_4 y z w a b)*(c5_2 y z w a b))+(((c4_5 y z w a b)*(c5_1 y z w a b))+(((c4_6 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_4 y z w a b)*(c7_2 y z w a b))+(((c6_5 y z w a b)*(c7_1 y z w a b))+(((c6_6 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_3 y z w a b)*(c9_3 y z w a b))+(((c8_4 y z w a b)*(c9_2 y z w a b))+(((c8_5 y z w a b)*(c9_1 y z w a b))+(((c8_6 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_6 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c10_6,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_4,c2_5,c2_6,c3_0,c3_1,c3_2,c4_4,c4_5,c4_6,c5_0,c5_1,c5_2,c6_4,c6_5,c6_6,c7_0,c7_1,c7_2,c8_3,c8_4,c8_5,c8_6,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_6
theorem coefficient_7 (y z w a b : ℂ) : (certificate y z w a b)[7]?=some 0 := by
  change some (((((((((c0_1 y z w a b)*(c1_6 y z w a b))+(((c0_2 y z w a b)*(c1_5 y z w a b))+(((c0_3 y z w a b)*(c1_4 y z w a b))+(((c0_4 y z w a b)*(c1_3 y z w a b))+(((c0_5 y z w a b)*(c1_2 y z w a b))+(((c0_6 y z w a b)*(c1_1 y z w a b))+(((c0_7 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*(((c2_5 y z w a b)*(c3_2 y z w a b))+(((c2_6 y z w a b)*(c3_1 y z w a b))+(((c2_7 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_5 y z w a b)*(c5_2 y z w a b))+(((c4_6 y z w a b)*(c5_1 y z w a b))+(((c4_7 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_5 y z w a b)*(c7_2 y z w a b))+(((c6_6 y z w a b)*(c7_1 y z w a b))+(((c6_7 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_4 y z w a b)*(c9_3 y z w a b))+(((c8_5 y z w a b)*(c9_2 y z w a b))+(((c8_6 y z w a b)*(c9_1 y z w a b))+(((c8_7 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_7 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c10_7,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_5,c2_6,c2_7,c3_0,c3_1,c3_2,c4_5,c4_6,c4_7,c5_0,c5_1,c5_2,c6_5,c6_6,c6_7,c7_0,c7_1,c7_2,c8_4,c8_5,c8_6,c8_7,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_7

theorem coefficient_8 (y z w a b : ℂ) : (certificate y z w a b)[8]?=some 0 := by
  change some (((((((((c0_2 y z w a b)*(c1_6 y z w a b))+(((c0_3 y z w a b)*(c1_5 y z w a b))+(((c0_4 y z w a b)*(c1_4 y z w a b))+(((c0_5 y z w a b)*(c1_3 y z w a b))+(((c0_6 y z w a b)*(c1_2 y z w a b))+(((c0_7 y z w a b)*(c1_1 y z w a b))+(((c0_8 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*(((c2_6 y z w a b)*(c3_2 y z w a b))+(((c2_7 y z w a b)*(c3_1 y z w a b))+(((c2_8 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_6 y z w a b)*(c5_2 y z w a b))+(((c4_7 y z w a b)*(c5_1 y z w a b))+(((c4_8 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_6 y z w a b)*(c7_2 y z w a b))+(((c6_7 y z w a b)*(c7_1 y z w a b))+(((c6_8 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_5 y z w a b)*(c9_3 y z w a b))+(((c8_6 y z w a b)*(c9_2 y z w a b))+(((c8_7 y z w a b)*(c9_1 y z w a b))+(((c8_8 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_8 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c10_8,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_6,c2_7,c2_8,c3_0,c3_1,c3_2,c4_6,c4_7,c4_8,c5_0,c5_1,c5_2,c6_6,c6_7,c6_8,c7_0,c7_1,c7_2,c8_5,c8_6,c8_7,c8_8,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_8
theorem coefficient_9 (y z w a b : ℂ) : (certificate y z w a b)[9]?=some 0 := by
  change some (((((((((c0_3 y z w a b)*(c1_6 y z w a b))+(((c0_4 y z w a b)*(c1_5 y z w a b))+(((c0_5 y z w a b)*(c1_4 y z w a b))+(((c0_6 y z w a b)*(c1_3 y z w a b))+(((c0_7 y z w a b)*(c1_2 y z w a b))+((c0_8 y z w a b)*(c1_1 y z w a b)))))))+((-1)*(((c2_7 y z w a b)*(c3_2 y z w a b))+(((c2_8 y z w a b)*(c3_1 y z w a b))+(((c2_9 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_7 y z w a b)*(c5_2 y z w a b))+(((c4_8 y z w a b)*(c5_1 y z w a b))+(((c4_9 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_7 y z w a b)*(c7_2 y z w a b))+(((c6_8 y z w a b)*(c7_1 y z w a b))+(((c6_9 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_6 y z w a b)*(c9_3 y z w a b))+(((c8_7 y z w a b)*(c9_2 y z w a b))+(((c8_8 y z w a b)*(c9_1 y z w a b))+(((c8_9 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_9 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c10_9,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_2,c4_7,c4_8,c4_9,c5_0,c5_1,c5_2,c6_7,c6_8,c6_9,c7_0,c7_1,c7_2,c8_6,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_9

theorem coefficient_10 (y z w a b : ℂ) : (certificate y z w a b)[10]?=some 0 := by
  change some (((((((((c0_4 y z w a b)*(c1_6 y z w a b))+(((c0_5 y z w a b)*(c1_5 y z w a b))+(((c0_6 y z w a b)*(c1_4 y z w a b))+(((c0_7 y z w a b)*(c1_3 y z w a b))+((c0_8 y z w a b)*(c1_2 y z w a b))))))+((-1)*(((c2_8 y z w a b)*(c3_2 y z w a b))+(((c2_9 y z w a b)*(c3_1 y z w a b))+(((c2_10 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_8 y z w a b)*(c5_2 y z w a b))+(((c4_9 y z w a b)*(c5_1 y z w a b))+(((c4_10 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_8 y z w a b)*(c7_2 y z w a b))+((c6_9 y z w a b)*(c7_1 y z w a b)))))+((-1)*(((c8_7 y z w a b)*(c9_3 y z w a b))+(((c8_8 y z w a b)*(c9_2 y z w a b))+(((c8_9 y z w a b)*(c9_1 y z w a b))+(((c8_10 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_10 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_4,c0_5,c0_6,c0_7,c0_8,c10_10,c1_2,c1_3,c1_4,c1_5,c1_6,c2_10,c2_8,c2_9,c3_0,c3_1,c3_2,c4_10,c4_8,c4_9,c5_0,c5_1,c5_2,c6_8,c6_9,c7_1,c7_2,c8_10,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_10
theorem coefficient_11 (y z w a b : ℂ) : (certificate y z w a b)[11]?=some 0 := by
  change some (((((((((c0_5 y z w a b)*(c1_6 y z w a b))+(((c0_6 y z w a b)*(c1_5 y z w a b))+(((c0_7 y z w a b)*(c1_4 y z w a b))+((c0_8 y z w a b)*(c1_3 y z w a b)))))+((-1)*(((c2_9 y z w a b)*(c3_2 y z w a b))+(((c2_10 y z w a b)*(c3_1 y z w a b))+(((c2_11 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_9 y z w a b)*(c5_2 y z w a b))+(((c4_10 y z w a b)*(c5_1 y z w a b))+(((c4_11 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*((c6_9 y z w a b)*(c7_2 y z w a b))))+((-1)*(((c8_8 y z w a b)*(c9_3 y z w a b))+(((c8_9 y z w a b)*(c9_2 y z w a b))+((c8_10 y z w a b)*(c9_1 y z w a b))))))+((-1)*(c10_11 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_5,c0_6,c0_7,c0_8,c10_11,c1_3,c1_4,c1_5,c1_6,c2_10,c2_11,c2_9,c3_0,c3_1,c3_2,c4_10,c4_11,c4_9,c5_0,c5_1,c5_2,c6_9,c7_2,c8_10,c8_8,c8_9,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_11

theorem coefficient_12 (y z w a b : ℂ) : (certificate y z w a b)[12]?=some 0 := by
  change some ((((((((c0_6 y z w a b)*(c1_6 y z w a b))+(((c0_7 y z w a b)*(c1_5 y z w a b))+((c0_8 y z w a b)*(c1_4 y z w a b))))+((-1)*(((c2_10 y z w a b)*(c3_2 y z w a b))+((c2_11 y z w a b)*(c3_1 y z w a b)))))+((-1)*(((c4_10 y z w a b)*(c5_2 y z w a b))+(((c4_11 y z w a b)*(c5_1 y z w a b))+(((c4_12 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c8_9 y z w a b)*(c9_3 y z w a b))+((c8_10 y z w a b)*(c9_2 y z w a b)))))+((-1)*(c10_12 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_6,c0_7,c0_8,c10_12,c1_4,c1_5,c1_6,c2_10,c2_11,c3_1,c3_2,c4_10,c4_11,c4_12,c5_0,c5_1,c5_2,c8_10,c8_9,c9_2,c9_3]
  ring
#print axioms coefficient_12
theorem coefficient_13 (y z w a b : ℂ) : (certificate y z w a b)[13]?=some 0 := by
  change some ((((((((c0_7 y z w a b)*(c1_6 y z w a b))+((c0_8 y z w a b)*(c1_5 y z w a b)))+((-1)*((c2_11 y z w a b)*(c3_2 y z w a b))))+((-1)*(((c4_11 y z w a b)*(c5_2 y z w a b))+((c4_12 y z w a b)*(c5_1 y z w a b)))))+((-1)*((c8_10 y z w a b)*(c9_3 y z w a b))))+((-1)*(c10_13 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_7,c0_8,c10_13,c1_5,c1_6,c2_11,c3_2,c4_11,c4_12,c5_1,c5_2,c8_10,c9_3]
  ring
#print axioms coefficient_13

theorem coefficient_14 (y z w a b : ℂ) : (certificate y z w a b)[14]?=some 0 := by
  change some (((((c0_8 y z w a b)*(c1_6 y z w a b))+((-1)*((c4_12 y z w a b)*(c5_2 y z w a b))))+((-1)*(c10_14 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_8,c10_14,c1_6,c4_12,c5_2]
  ring
#print axioms coefficient_14

end SmallLevelTwentySixMMPPariSyzygy6Column1
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariSyzygy6Column2
open SmallLevelPolynomialCoefficientCertificate

theorem coefficient_0 (y z w a b : ℂ) : (certificate y z w a b)[0]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_0 y z w a b))+0)+((-1)*(((c2_0 y z w a b)*(c3_0 y z w a b))+0)))+((-1)*(((c4_0 y z w a b)*(c5_0 y z w a b))+0)))+((-1)*(((c6_0 y z w a b)*(c7_0 y z w a b))+0)))+((-1)*(((c8_0 y z w a b)*(c9_0 y z w a b))+0))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c1_0,c2_0,c3_0,c4_0,c5_0,c6_0,c7_0,c8_0,c9_0]
  ring
#print axioms coefficient_0
theorem coefficient_1 (y z w a b : ℂ) : (certificate y z w a b)[1]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_1 y z w a b))+(((c0_1 y z w a b)*(c1_0 y z w a b))+0))+((-1)*(((c2_0 y z w a b)*(c3_1 y z w a b))+(((c2_1 y z w a b)*(c3_0 y z w a b))+0))))+((-1)*(((c4_0 y z w a b)*(c5_1 y z w a b))+(((c4_1 y z w a b)*(c5_0 y z w a b))+0))))+((-1)*(((c6_0 y z w a b)*(c7_1 y z w a b))+(((c6_1 y z w a b)*(c7_0 y z w a b))+0))))+((-1)*(((c8_0 y z w a b)*(c9_1 y z w a b))+(((c8_1 y z w a b)*(c9_0 y z w a b))+0)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c1_0,c1_1,c2_0,c2_1,c3_0,c3_1,c4_0,c4_1,c5_0,c5_1,c6_0,c6_1,c7_0,c7_1,c8_0,c8_1,c9_0,c9_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (y z w a b : ℂ) : (certificate y z w a b)[2]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_2 y z w a b))+(((c0_1 y z w a b)*(c1_1 y z w a b))+(((c0_2 y z w a b)*(c1_0 y z w a b))+0)))+((-1)*(((c2_0 y z w a b)*(c3_2 y z w a b))+(((c2_1 y z w a b)*(c3_1 y z w a b))+(((c2_2 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_0 y z w a b)*(c5_2 y z w a b))+(((c4_1 y z w a b)*(c5_1 y z w a b))+(((c4_2 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_0 y z w a b)*(c7_2 y z w a b))+(((c6_1 y z w a b)*(c7_1 y z w a b))+(((c6_2 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_2 y z w a b))+(((c8_1 y z w a b)*(c9_1 y z w a b))+(((c8_2 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c1_0,c1_1,c1_2,c2_0,c2_1,c2_2,c3_0,c3_1,c3_2,c4_0,c4_1,c4_2,c5_0,c5_1,c5_2,c6_0,c6_1,c6_2,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_2
theorem coefficient_3 (y z w a b : ℂ) : (certificate y z w a b)[3]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_3 y z w a b))+(((c0_1 y z w a b)*(c1_2 y z w a b))+(((c0_2 y z w a b)*(c1_1 y z w a b))+(((c0_3 y z w a b)*(c1_0 y z w a b))+0))))+((-1)*(((c2_0 y z w a b)*(c3_3 y z w a b))+(((c2_1 y z w a b)*(c3_2 y z w a b))+(((c2_2 y z w a b)*(c3_1 y z w a b))+(((c2_3 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_0 y z w a b)*(c5_3 y z w a b))+(((c4_1 y z w a b)*(c5_2 y z w a b))+(((c4_2 y z w a b)*(c5_1 y z w a b))+(((c4_3 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_0 y z w a b)*(c7_3 y z w a b))+(((c6_1 y z w a b)*(c7_2 y z w a b))+(((c6_2 y z w a b)*(c7_1 y z w a b))+(((c6_3 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_0 y z w a b)*(c9_3 y z w a b))+(((c8_1 y z w a b)*(c9_2 y z w a b))+(((c8_2 y z w a b)*(c9_1 y z w a b))+(((c8_3 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c3_0,c3_1,c3_2,c3_3,c4_0,c4_1,c4_2,c4_3,c5_0,c5_1,c5_2,c5_3,c6_0,c6_1,c6_2,c6_3,c7_0,c7_1,c7_2,c7_3,c8_0,c8_1,c8_2,c8_3,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (y z w a b : ℂ) : (certificate y z w a b)[4]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_4 y z w a b))+(((c0_1 y z w a b)*(c1_3 y z w a b))+(((c0_2 y z w a b)*(c1_2 y z w a b))+(((c0_3 y z w a b)*(c1_1 y z w a b))+(((c0_4 y z w a b)*(c1_0 y z w a b))+0)))))+((-1)*(((c2_1 y z w a b)*(c3_3 y z w a b))+(((c2_2 y z w a b)*(c3_2 y z w a b))+(((c2_3 y z w a b)*(c3_1 y z w a b))+(((c2_4 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_1 y z w a b)*(c5_3 y z w a b))+(((c4_2 y z w a b)*(c5_2 y z w a b))+(((c4_3 y z w a b)*(c5_1 y z w a b))+(((c4_4 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_1 y z w a b)*(c7_3 y z w a b))+(((c6_2 y z w a b)*(c7_2 y z w a b))+(((c6_3 y z w a b)*(c7_1 y z w a b))+(((c6_4 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_0 y z w a b)*(c9_4 y z w a b))+(((c8_1 y z w a b)*(c9_3 y z w a b))+(((c8_2 y z w a b)*(c9_2 y z w a b))+(((c8_3 y z w a b)*(c9_1 y z w a b))+(((c8_4 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_0,c1_1,c1_2,c1_3,c1_4,c2_1,c2_2,c2_3,c2_4,c3_0,c3_1,c3_2,c3_3,c4_1,c4_2,c4_3,c4_4,c5_0,c5_1,c5_2,c5_3,c6_1,c6_2,c6_3,c6_4,c7_0,c7_1,c7_2,c7_3,c8_0,c8_1,c8_2,c8_3,c8_4,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_4
theorem coefficient_5 (y z w a b : ℂ) : (certificate y z w a b)[5]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_5 y z w a b))+(((c0_1 y z w a b)*(c1_4 y z w a b))+(((c0_2 y z w a b)*(c1_3 y z w a b))+(((c0_3 y z w a b)*(c1_2 y z w a b))+(((c0_4 y z w a b)*(c1_1 y z w a b))+(((c0_5 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*(((c2_2 y z w a b)*(c3_3 y z w a b))+(((c2_3 y z w a b)*(c3_2 y z w a b))+(((c2_4 y z w a b)*(c3_1 y z w a b))+(((c2_5 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_2 y z w a b)*(c5_3 y z w a b))+(((c4_3 y z w a b)*(c5_2 y z w a b))+(((c4_4 y z w a b)*(c5_1 y z w a b))+(((c4_5 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_2 y z w a b)*(c7_3 y z w a b))+(((c6_3 y z w a b)*(c7_2 y z w a b))+(((c6_4 y z w a b)*(c7_1 y z w a b))+(((c6_5 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_1 y z w a b)*(c9_4 y z w a b))+(((c8_2 y z w a b)*(c9_3 y z w a b))+(((c8_3 y z w a b)*(c9_2 y z w a b))+(((c8_4 y z w a b)*(c9_1 y z w a b))+(((c8_5 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_2,c2_3,c2_4,c2_5,c3_0,c3_1,c3_2,c3_3,c4_2,c4_3,c4_4,c4_5,c5_0,c5_1,c5_2,c5_3,c6_2,c6_3,c6_4,c6_5,c7_0,c7_1,c7_2,c7_3,c8_1,c8_2,c8_3,c8_4,c8_5,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_5

theorem coefficient_6 (y z w a b : ℂ) : (certificate y z w a b)[6]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_6 y z w a b))+(((c0_1 y z w a b)*(c1_5 y z w a b))+(((c0_2 y z w a b)*(c1_4 y z w a b))+(((c0_3 y z w a b)*(c1_3 y z w a b))+(((c0_4 y z w a b)*(c1_2 y z w a b))+(((c0_5 y z w a b)*(c1_1 y z w a b))+(((c0_6 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*(((c2_3 y z w a b)*(c3_3 y z w a b))+(((c2_4 y z w a b)*(c3_2 y z w a b))+(((c2_5 y z w a b)*(c3_1 y z w a b))+(((c2_6 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_3 y z w a b)*(c5_3 y z w a b))+(((c4_4 y z w a b)*(c5_2 y z w a b))+(((c4_5 y z w a b)*(c5_1 y z w a b))+(((c4_6 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_3 y z w a b)*(c7_3 y z w a b))+(((c6_4 y z w a b)*(c7_2 y z w a b))+(((c6_5 y z w a b)*(c7_1 y z w a b))+(((c6_6 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_2 y z w a b)*(c9_4 y z w a b))+(((c8_3 y z w a b)*(c9_3 y z w a b))+(((c8_4 y z w a b)*(c9_2 y z w a b))+(((c8_5 y z w a b)*(c9_1 y z w a b))+(((c8_6 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_3,c2_4,c2_5,c2_6,c3_0,c3_1,c3_2,c3_3,c4_3,c4_4,c4_5,c4_6,c5_0,c5_1,c5_2,c5_3,c6_3,c6_4,c6_5,c6_6,c7_0,c7_1,c7_2,c7_3,c8_2,c8_3,c8_4,c8_5,c8_6,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_6
theorem coefficient_7 (y z w a b : ℂ) : (certificate y z w a b)[7]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_7 y z w a b))+(((c0_1 y z w a b)*(c1_6 y z w a b))+(((c0_2 y z w a b)*(c1_5 y z w a b))+(((c0_3 y z w a b)*(c1_4 y z w a b))+(((c0_4 y z w a b)*(c1_3 y z w a b))+(((c0_5 y z w a b)*(c1_2 y z w a b))+(((c0_6 y z w a b)*(c1_1 y z w a b))+(((c0_7 y z w a b)*(c1_0 y z w a b))+0))))))))+((-1)*(((c2_4 y z w a b)*(c3_3 y z w a b))+(((c2_5 y z w a b)*(c3_2 y z w a b))+(((c2_6 y z w a b)*(c3_1 y z w a b))+(((c2_7 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_4 y z w a b)*(c5_3 y z w a b))+(((c4_5 y z w a b)*(c5_2 y z w a b))+(((c4_6 y z w a b)*(c5_1 y z w a b))+(((c4_7 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_4 y z w a b)*(c7_3 y z w a b))+(((c6_5 y z w a b)*(c7_2 y z w a b))+(((c6_6 y z w a b)*(c7_1 y z w a b))+(((c6_7 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_3 y z w a b)*(c9_4 y z w a b))+(((c8_4 y z w a b)*(c9_3 y z w a b))+(((c8_5 y z w a b)*(c9_2 y z w a b))+(((c8_6 y z w a b)*(c9_1 y z w a b))+(((c8_7 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c2_4,c2_5,c2_6,c2_7,c3_0,c3_1,c3_2,c3_3,c4_4,c4_5,c4_6,c4_7,c5_0,c5_1,c5_2,c5_3,c6_4,c6_5,c6_6,c6_7,c7_0,c7_1,c7_2,c7_3,c8_3,c8_4,c8_5,c8_6,c8_7,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_7

theorem coefficient_8 (y z w a b : ℂ) : (certificate y z w a b)[8]?=some 0 := by
  change some ((((((((c0_1 y z w a b)*(c1_7 y z w a b))+(((c0_2 y z w a b)*(c1_6 y z w a b))+(((c0_3 y z w a b)*(c1_5 y z w a b))+(((c0_4 y z w a b)*(c1_4 y z w a b))+(((c0_5 y z w a b)*(c1_3 y z w a b))+(((c0_6 y z w a b)*(c1_2 y z w a b))+(((c0_7 y z w a b)*(c1_1 y z w a b))+(((c0_8 y z w a b)*(c1_0 y z w a b))+0))))))))+((-1)*(((c2_5 y z w a b)*(c3_3 y z w a b))+(((c2_6 y z w a b)*(c3_2 y z w a b))+(((c2_7 y z w a b)*(c3_1 y z w a b))+(((c2_8 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_5 y z w a b)*(c5_3 y z w a b))+(((c4_6 y z w a b)*(c5_2 y z w a b))+(((c4_7 y z w a b)*(c5_1 y z w a b))+(((c4_8 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_5 y z w a b)*(c7_3 y z w a b))+(((c6_6 y z w a b)*(c7_2 y z w a b))+(((c6_7 y z w a b)*(c7_1 y z w a b))+(((c6_8 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_4 y z w a b)*(c9_4 y z w a b))+(((c8_5 y z w a b)*(c9_3 y z w a b))+(((c8_6 y z w a b)*(c9_2 y z w a b))+(((c8_7 y z w a b)*(c9_1 y z w a b))+(((c8_8 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c2_5,c2_6,c2_7,c2_8,c3_0,c3_1,c3_2,c3_3,c4_5,c4_6,c4_7,c4_8,c5_0,c5_1,c5_2,c5_3,c6_5,c6_6,c6_7,c6_8,c7_0,c7_1,c7_2,c7_3,c8_4,c8_5,c8_6,c8_7,c8_8,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_8
theorem coefficient_9 (y z w a b : ℂ) : (certificate y z w a b)[9]?=some 0 := by
  change some ((((((((c0_2 y z w a b)*(c1_7 y z w a b))+(((c0_3 y z w a b)*(c1_6 y z w a b))+(((c0_4 y z w a b)*(c1_5 y z w a b))+(((c0_5 y z w a b)*(c1_4 y z w a b))+(((c0_6 y z w a b)*(c1_3 y z w a b))+(((c0_7 y z w a b)*(c1_2 y z w a b))+((c0_8 y z w a b)*(c1_1 y z w a b))))))))+((-1)*(((c2_6 y z w a b)*(c3_3 y z w a b))+(((c2_7 y z w a b)*(c3_2 y z w a b))+(((c2_8 y z w a b)*(c3_1 y z w a b))+(((c2_9 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_6 y z w a b)*(c5_3 y z w a b))+(((c4_7 y z w a b)*(c5_2 y z w a b))+(((c4_8 y z w a b)*(c5_1 y z w a b))+(((c4_9 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_6 y z w a b)*(c7_3 y z w a b))+(((c6_7 y z w a b)*(c7_2 y z w a b))+(((c6_8 y z w a b)*(c7_1 y z w a b))+(((c6_9 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_5 y z w a b)*(c9_4 y z w a b))+(((c8_6 y z w a b)*(c9_3 y z w a b))+(((c8_7 y z w a b)*(c9_2 y z w a b))+(((c8_8 y z w a b)*(c9_1 y z w a b))+(((c8_9 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_2,c3_3,c4_6,c4_7,c4_8,c4_9,c5_0,c5_1,c5_2,c5_3,c6_6,c6_7,c6_8,c6_9,c7_0,c7_1,c7_2,c7_3,c8_5,c8_6,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_9

theorem coefficient_10 (y z w a b : ℂ) : (certificate y z w a b)[10]?=some 0 := by
  change some ((((((((c0_3 y z w a b)*(c1_7 y z w a b))+(((c0_4 y z w a b)*(c1_6 y z w a b))+(((c0_5 y z w a b)*(c1_5 y z w a b))+(((c0_6 y z w a b)*(c1_4 y z w a b))+(((c0_7 y z w a b)*(c1_3 y z w a b))+((c0_8 y z w a b)*(c1_2 y z w a b)))))))+((-1)*(((c2_7 y z w a b)*(c3_3 y z w a b))+(((c2_8 y z w a b)*(c3_2 y z w a b))+(((c2_9 y z w a b)*(c3_1 y z w a b))+(((c2_10 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_7 y z w a b)*(c5_3 y z w a b))+(((c4_8 y z w a b)*(c5_2 y z w a b))+(((c4_9 y z w a b)*(c5_1 y z w a b))+(((c4_10 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_7 y z w a b)*(c7_3 y z w a b))+(((c6_8 y z w a b)*(c7_2 y z w a b))+((c6_9 y z w a b)*(c7_1 y z w a b))))))+((-1)*(((c8_6 y z w a b)*(c9_4 y z w a b))+(((c8_7 y z w a b)*(c9_3 y z w a b))+(((c8_8 y z w a b)*(c9_2 y z w a b))+(((c8_9 y z w a b)*(c9_1 y z w a b))+(((c8_10 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c2_10,c2_7,c2_8,c2_9,c3_0,c3_1,c3_2,c3_3,c4_10,c4_7,c4_8,c4_9,c5_0,c5_1,c5_2,c5_3,c6_7,c6_8,c6_9,c7_1,c7_2,c7_3,c8_10,c8_6,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_10
theorem coefficient_11 (y z w a b : ℂ) : (certificate y z w a b)[11]?=some 0 := by
  change some ((((((((c0_4 y z w a b)*(c1_7 y z w a b))+(((c0_5 y z w a b)*(c1_6 y z w a b))+(((c0_6 y z w a b)*(c1_5 y z w a b))+(((c0_7 y z w a b)*(c1_4 y z w a b))+((c0_8 y z w a b)*(c1_3 y z w a b))))))+((-1)*(((c2_8 y z w a b)*(c3_3 y z w a b))+(((c2_9 y z w a b)*(c3_2 y z w a b))+(((c2_10 y z w a b)*(c3_1 y z w a b))+(((c2_11 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_8 y z w a b)*(c5_3 y z w a b))+(((c4_9 y z w a b)*(c5_2 y z w a b))+(((c4_10 y z w a b)*(c5_1 y z w a b))+(((c4_11 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_8 y z w a b)*(c7_3 y z w a b))+((c6_9 y z w a b)*(c7_2 y z w a b)))))+((-1)*(((c8_7 y z w a b)*(c9_4 y z w a b))+(((c8_8 y z w a b)*(c9_3 y z w a b))+(((c8_9 y z w a b)*(c9_2 y z w a b))+((c8_10 y z w a b)*(c9_1 y z w a b))))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_4,c0_5,c0_6,c0_7,c0_8,c1_3,c1_4,c1_5,c1_6,c1_7,c2_10,c2_11,c2_8,c2_9,c3_0,c3_1,c3_2,c3_3,c4_10,c4_11,c4_8,c4_9,c5_0,c5_1,c5_2,c5_3,c6_8,c6_9,c7_2,c7_3,c8_10,c8_7,c8_8,c8_9,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_11

theorem coefficient_12 (y z w a b : ℂ) : (certificate y z w a b)[12]?=some 0 := by
  change some ((((((((c0_5 y z w a b)*(c1_7 y z w a b))+(((c0_6 y z w a b)*(c1_6 y z w a b))+(((c0_7 y z w a b)*(c1_5 y z w a b))+((c0_8 y z w a b)*(c1_4 y z w a b)))))+((-1)*(((c2_9 y z w a b)*(c3_3 y z w a b))+(((c2_10 y z w a b)*(c3_2 y z w a b))+((c2_11 y z w a b)*(c3_1 y z w a b))))))+((-1)*(((c4_9 y z w a b)*(c5_3 y z w a b))+(((c4_10 y z w a b)*(c5_2 y z w a b))+(((c4_11 y z w a b)*(c5_1 y z w a b))+(((c4_12 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*((c6_9 y z w a b)*(c7_3 y z w a b))))+((-1)*(((c8_8 y z w a b)*(c9_4 y z w a b))+(((c8_9 y z w a b)*(c9_3 y z w a b))+((c8_10 y z w a b)*(c9_2 y z w a b)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_5,c0_6,c0_7,c0_8,c1_4,c1_5,c1_6,c1_7,c2_10,c2_11,c2_9,c3_1,c3_2,c3_3,c4_10,c4_11,c4_12,c4_9,c5_0,c5_1,c5_2,c5_3,c6_9,c7_3,c8_10,c8_8,c8_9,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_12
theorem coefficient_13 (y z w a b : ℂ) : (certificate y z w a b)[13]?=some 0 := by
  change some (((((((c0_6 y z w a b)*(c1_7 y z w a b))+(((c0_7 y z w a b)*(c1_6 y z w a b))+((c0_8 y z w a b)*(c1_5 y z w a b))))+((-1)*(((c2_10 y z w a b)*(c3_3 y z w a b))+((c2_11 y z w a b)*(c3_2 y z w a b)))))+((-1)*(((c4_10 y z w a b)*(c5_3 y z w a b))+(((c4_11 y z w a b)*(c5_2 y z w a b))+((c4_12 y z w a b)*(c5_1 y z w a b))))))+((-1)*(((c8_9 y z w a b)*(c9_4 y z w a b))+((c8_10 y z w a b)*(c9_3 y z w a b))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_6,c0_7,c0_8,c1_5,c1_6,c1_7,c2_10,c2_11,c3_2,c3_3,c4_10,c4_11,c4_12,c5_1,c5_2,c5_3,c8_10,c8_9,c9_3,c9_4]
  ring
#print axioms coefficient_13

theorem coefficient_14 (y z w a b : ℂ) : (certificate y z w a b)[14]?=some 0 := by
  change some (((((((c0_7 y z w a b)*(c1_7 y z w a b))+((c0_8 y z w a b)*(c1_6 y z w a b)))+((-1)*((c2_11 y z w a b)*(c3_3 y z w a b))))+((-1)*(((c4_11 y z w a b)*(c5_3 y z w a b))+((c4_12 y z w a b)*(c5_2 y z w a b)))))+((-1)*((c8_10 y z w a b)*(c9_4 y z w a b)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_7,c0_8,c1_6,c1_7,c2_11,c3_3,c4_11,c4_12,c5_2,c5_3,c8_10,c9_4]
  ring
#print axioms coefficient_14
theorem coefficient_15 (y z w a b : ℂ) : (certificate y z w a b)[15]?=some 0 := by
  change some ((((c0_8 y z w a b)*(c1_7 y z w a b))+((-1)*((c4_12 y z w a b)*(c5_3 y z w a b)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_8,c1_7,c4_12,c5_3]
  ring
#print axioms coefficient_15

end SmallLevelTwentySixMMPPariSyzygy6Column2
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariSyzygy6Column3
open SmallLevelPolynomialCoefficientCertificate

theorem coefficient_0 (y z w a b : ℂ) : (certificate y z w a b)[0]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_0 y z w a b))+0)+((-1)*(((c2_0 y z w a b)*(c3_0 y z w a b))+0)))+((-1)*(((c4_0 y z w a b)*(c5_0 y z w a b))+0)))+((-1)*(((c6_0 y z w a b)*(c7_0 y z w a b))+0)))+((-1)*(((c8_0 y z w a b)*(c9_0 y z w a b))+0))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c1_0,c2_0,c3_0,c4_0,c5_0,c6_0,c7_0,c8_0,c9_0]
  ring
#print axioms coefficient_0
theorem coefficient_1 (y z w a b : ℂ) : (certificate y z w a b)[1]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_1 y z w a b))+(((c0_1 y z w a b)*(c1_0 y z w a b))+0))+((-1)*(((c2_0 y z w a b)*(c3_1 y z w a b))+(((c2_1 y z w a b)*(c3_0 y z w a b))+0))))+((-1)*(((c4_0 y z w a b)*(c5_1 y z w a b))+(((c4_1 y z w a b)*(c5_0 y z w a b))+0))))+((-1)*(((c6_0 y z w a b)*(c7_1 y z w a b))+(((c6_1 y z w a b)*(c7_0 y z w a b))+0))))+((-1)*(((c8_0 y z w a b)*(c9_1 y z w a b))+(((c8_1 y z w a b)*(c9_0 y z w a b))+0)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c1_0,c1_1,c2_0,c2_1,c3_0,c3_1,c4_0,c4_1,c5_0,c5_1,c6_0,c6_1,c7_0,c7_1,c8_0,c8_1,c9_0,c9_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (y z w a b : ℂ) : (certificate y z w a b)[2]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_2 y z w a b))+(((c0_1 y z w a b)*(c1_1 y z w a b))+(((c0_2 y z w a b)*(c1_0 y z w a b))+0)))+((-1)*(((c2_0 y z w a b)*(c3_2 y z w a b))+(((c2_1 y z w a b)*(c3_1 y z w a b))+(((c2_2 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_0 y z w a b)*(c5_2 y z w a b))+(((c4_1 y z w a b)*(c5_1 y z w a b))+(((c4_2 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_0 y z w a b)*(c7_2 y z w a b))+(((c6_1 y z w a b)*(c7_1 y z w a b))+(((c6_2 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_2 y z w a b))+(((c8_1 y z w a b)*(c9_1 y z w a b))+(((c8_2 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c1_0,c1_1,c1_2,c2_0,c2_1,c2_2,c3_0,c3_1,c3_2,c4_0,c4_1,c4_2,c5_0,c5_1,c5_2,c6_0,c6_1,c6_2,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_2
theorem coefficient_3 (y z w a b : ℂ) : (certificate y z w a b)[3]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_3 y z w a b))+(((c0_1 y z w a b)*(c1_2 y z w a b))+(((c0_2 y z w a b)*(c1_1 y z w a b))+(((c0_3 y z w a b)*(c1_0 y z w a b))+0))))+((-1)*(((c2_1 y z w a b)*(c3_2 y z w a b))+(((c2_2 y z w a b)*(c3_1 y z w a b))+(((c2_3 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_1 y z w a b)*(c5_2 y z w a b))+(((c4_2 y z w a b)*(c5_1 y z w a b))+(((c4_3 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_1 y z w a b)*(c7_2 y z w a b))+(((c6_2 y z w a b)*(c7_1 y z w a b))+(((c6_3 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_3 y z w a b))+(((c8_1 y z w a b)*(c9_2 y z w a b))+(((c8_2 y z w a b)*(c9_1 y z w a b))+(((c8_3 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c1_0,c1_1,c1_2,c1_3,c2_1,c2_2,c2_3,c3_0,c3_1,c3_2,c4_1,c4_2,c4_3,c5_0,c5_1,c5_2,c6_1,c6_2,c6_3,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c8_3,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (y z w a b : ℂ) : (certificate y z w a b)[4]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_4 y z w a b))+(((c0_1 y z w a b)*(c1_3 y z w a b))+(((c0_2 y z w a b)*(c1_2 y z w a b))+(((c0_3 y z w a b)*(c1_1 y z w a b))+(((c0_4 y z w a b)*(c1_0 y z w a b))+0)))))+((-1)*(((c2_2 y z w a b)*(c3_2 y z w a b))+(((c2_3 y z w a b)*(c3_1 y z w a b))+(((c2_4 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_2 y z w a b)*(c5_2 y z w a b))+(((c4_3 y z w a b)*(c5_1 y z w a b))+(((c4_4 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_2 y z w a b)*(c7_2 y z w a b))+(((c6_3 y z w a b)*(c7_1 y z w a b))+(((c6_4 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_1 y z w a b)*(c9_3 y z w a b))+(((c8_2 y z w a b)*(c9_2 y z w a b))+(((c8_3 y z w a b)*(c9_1 y z w a b))+(((c8_4 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_0,c1_1,c1_2,c1_3,c1_4,c2_2,c2_3,c2_4,c3_0,c3_1,c3_2,c4_2,c4_3,c4_4,c5_0,c5_1,c5_2,c6_2,c6_3,c6_4,c7_0,c7_1,c7_2,c8_1,c8_2,c8_3,c8_4,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_4
theorem coefficient_5 (y z w a b : ℂ) : (certificate y z w a b)[5]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_5 y z w a b))+(((c0_1 y z w a b)*(c1_4 y z w a b))+(((c0_2 y z w a b)*(c1_3 y z w a b))+(((c0_3 y z w a b)*(c1_2 y z w a b))+(((c0_4 y z w a b)*(c1_1 y z w a b))+(((c0_5 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*(((c2_3 y z w a b)*(c3_2 y z w a b))+(((c2_4 y z w a b)*(c3_1 y z w a b))+(((c2_5 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_3 y z w a b)*(c5_2 y z w a b))+(((c4_4 y z w a b)*(c5_1 y z w a b))+(((c4_5 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_3 y z w a b)*(c7_2 y z w a b))+(((c6_4 y z w a b)*(c7_1 y z w a b))+(((c6_5 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_2 y z w a b)*(c9_3 y z w a b))+(((c8_3 y z w a b)*(c9_2 y z w a b))+(((c8_4 y z w a b)*(c9_1 y z w a b))+(((c8_5 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_3,c2_4,c2_5,c3_0,c3_1,c3_2,c4_3,c4_4,c4_5,c5_0,c5_1,c5_2,c6_3,c6_4,c6_5,c7_0,c7_1,c7_2,c8_2,c8_3,c8_4,c8_5,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_5

theorem coefficient_6 (y z w a b : ℂ) : (certificate y z w a b)[6]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_6 y z w a b))+(((c0_1 y z w a b)*(c1_5 y z w a b))+(((c0_2 y z w a b)*(c1_4 y z w a b))+(((c0_3 y z w a b)*(c1_3 y z w a b))+(((c0_4 y z w a b)*(c1_2 y z w a b))+(((c0_5 y z w a b)*(c1_1 y z w a b))+(((c0_6 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*(((c2_4 y z w a b)*(c3_2 y z w a b))+(((c2_5 y z w a b)*(c3_1 y z w a b))+(((c2_6 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_4 y z w a b)*(c5_2 y z w a b))+(((c4_5 y z w a b)*(c5_1 y z w a b))+(((c4_6 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_4 y z w a b)*(c7_2 y z w a b))+(((c6_5 y z w a b)*(c7_1 y z w a b))+(((c6_6 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_3 y z w a b)*(c9_3 y z w a b))+(((c8_4 y z w a b)*(c9_2 y z w a b))+(((c8_5 y z w a b)*(c9_1 y z w a b))+(((c8_6 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_4,c2_5,c2_6,c3_0,c3_1,c3_2,c4_4,c4_5,c4_6,c5_0,c5_1,c5_2,c6_4,c6_5,c6_6,c7_0,c7_1,c7_2,c8_3,c8_4,c8_5,c8_6,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_6
theorem coefficient_7 (y z w a b : ℂ) : (certificate y z w a b)[7]?=some 0 := by
  change some ((((((((c0_1 y z w a b)*(c1_6 y z w a b))+(((c0_2 y z w a b)*(c1_5 y z w a b))+(((c0_3 y z w a b)*(c1_4 y z w a b))+(((c0_4 y z w a b)*(c1_3 y z w a b))+(((c0_5 y z w a b)*(c1_2 y z w a b))+(((c0_6 y z w a b)*(c1_1 y z w a b))+(((c0_7 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*(((c2_5 y z w a b)*(c3_2 y z w a b))+(((c2_6 y z w a b)*(c3_1 y z w a b))+(((c2_7 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_5 y z w a b)*(c5_2 y z w a b))+(((c4_6 y z w a b)*(c5_1 y z w a b))+(((c4_7 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_5 y z w a b)*(c7_2 y z w a b))+(((c6_6 y z w a b)*(c7_1 y z w a b))+(((c6_7 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_4 y z w a b)*(c9_3 y z w a b))+(((c8_5 y z w a b)*(c9_2 y z w a b))+(((c8_6 y z w a b)*(c9_1 y z w a b))+(((c8_7 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_5,c2_6,c2_7,c3_0,c3_1,c3_2,c4_5,c4_6,c4_7,c5_0,c5_1,c5_2,c6_5,c6_6,c6_7,c7_0,c7_1,c7_2,c8_4,c8_5,c8_6,c8_7,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_7

theorem coefficient_8 (y z w a b : ℂ) : (certificate y z w a b)[8]?=some 0 := by
  change some ((((((((c0_2 y z w a b)*(c1_6 y z w a b))+(((c0_3 y z w a b)*(c1_5 y z w a b))+(((c0_4 y z w a b)*(c1_4 y z w a b))+(((c0_5 y z w a b)*(c1_3 y z w a b))+(((c0_6 y z w a b)*(c1_2 y z w a b))+(((c0_7 y z w a b)*(c1_1 y z w a b))+(((c0_8 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*(((c2_6 y z w a b)*(c3_2 y z w a b))+(((c2_7 y z w a b)*(c3_1 y z w a b))+(((c2_8 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_6 y z w a b)*(c5_2 y z w a b))+(((c4_7 y z w a b)*(c5_1 y z w a b))+(((c4_8 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_6 y z w a b)*(c7_2 y z w a b))+(((c6_7 y z w a b)*(c7_1 y z w a b))+(((c6_8 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_5 y z w a b)*(c9_3 y z w a b))+(((c8_6 y z w a b)*(c9_2 y z w a b))+(((c8_7 y z w a b)*(c9_1 y z w a b))+(((c8_8 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_6,c2_7,c2_8,c3_0,c3_1,c3_2,c4_6,c4_7,c4_8,c5_0,c5_1,c5_2,c6_6,c6_7,c6_8,c7_0,c7_1,c7_2,c8_5,c8_6,c8_7,c8_8,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_8
theorem coefficient_9 (y z w a b : ℂ) : (certificate y z w a b)[9]?=some 0 := by
  change some ((((((((c0_3 y z w a b)*(c1_6 y z w a b))+(((c0_4 y z w a b)*(c1_5 y z w a b))+(((c0_5 y z w a b)*(c1_4 y z w a b))+(((c0_6 y z w a b)*(c1_3 y z w a b))+(((c0_7 y z w a b)*(c1_2 y z w a b))+((c0_8 y z w a b)*(c1_1 y z w a b)))))))+((-1)*(((c2_7 y z w a b)*(c3_2 y z w a b))+(((c2_8 y z w a b)*(c3_1 y z w a b))+(((c2_9 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_7 y z w a b)*(c5_2 y z w a b))+(((c4_8 y z w a b)*(c5_1 y z w a b))+(((c4_9 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_7 y z w a b)*(c7_2 y z w a b))+(((c6_8 y z w a b)*(c7_1 y z w a b))+(((c6_9 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_6 y z w a b)*(c9_3 y z w a b))+(((c8_7 y z w a b)*(c9_2 y z w a b))+(((c8_8 y z w a b)*(c9_1 y z w a b))+(((c8_9 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_2,c4_7,c4_8,c4_9,c5_0,c5_1,c5_2,c6_7,c6_8,c6_9,c7_0,c7_1,c7_2,c8_6,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_9

theorem coefficient_10 (y z w a b : ℂ) : (certificate y z w a b)[10]?=some 0 := by
  change some ((((((((c0_4 y z w a b)*(c1_6 y z w a b))+(((c0_5 y z w a b)*(c1_5 y z w a b))+(((c0_6 y z w a b)*(c1_4 y z w a b))+(((c0_7 y z w a b)*(c1_3 y z w a b))+((c0_8 y z w a b)*(c1_2 y z w a b))))))+((-1)*(((c2_8 y z w a b)*(c3_2 y z w a b))+(((c2_9 y z w a b)*(c3_1 y z w a b))+(((c2_10 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_8 y z w a b)*(c5_2 y z w a b))+(((c4_9 y z w a b)*(c5_1 y z w a b))+(((c4_10 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_8 y z w a b)*(c7_2 y z w a b))+((c6_9 y z w a b)*(c7_1 y z w a b)))))+((-1)*(((c8_7 y z w a b)*(c9_3 y z w a b))+(((c8_8 y z w a b)*(c9_2 y z w a b))+(((c8_9 y z w a b)*(c9_1 y z w a b))+(((c8_10 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_4,c0_5,c0_6,c0_7,c0_8,c1_2,c1_3,c1_4,c1_5,c1_6,c2_10,c2_8,c2_9,c3_0,c3_1,c3_2,c4_10,c4_8,c4_9,c5_0,c5_1,c5_2,c6_8,c6_9,c7_1,c7_2,c8_10,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_10
theorem coefficient_11 (y z w a b : ℂ) : (certificate y z w a b)[11]?=some 0 := by
  change some ((((((((c0_5 y z w a b)*(c1_6 y z w a b))+(((c0_6 y z w a b)*(c1_5 y z w a b))+(((c0_7 y z w a b)*(c1_4 y z w a b))+((c0_8 y z w a b)*(c1_3 y z w a b)))))+((-1)*(((c2_9 y z w a b)*(c3_2 y z w a b))+(((c2_10 y z w a b)*(c3_1 y z w a b))+(((c2_11 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_9 y z w a b)*(c5_2 y z w a b))+(((c4_10 y z w a b)*(c5_1 y z w a b))+(((c4_11 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*((c6_9 y z w a b)*(c7_2 y z w a b))))+((-1)*(((c8_8 y z w a b)*(c9_3 y z w a b))+(((c8_9 y z w a b)*(c9_2 y z w a b))+((c8_10 y z w a b)*(c9_1 y z w a b)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_5,c0_6,c0_7,c0_8,c1_3,c1_4,c1_5,c1_6,c2_10,c2_11,c2_9,c3_0,c3_1,c3_2,c4_10,c4_11,c4_9,c5_0,c5_1,c5_2,c6_9,c7_2,c8_10,c8_8,c8_9,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_11

theorem coefficient_12 (y z w a b : ℂ) : (certificate y z w a b)[12]?=some 0 := by
  change some (((((((c0_6 y z w a b)*(c1_6 y z w a b))+(((c0_7 y z w a b)*(c1_5 y z w a b))+((c0_8 y z w a b)*(c1_4 y z w a b))))+((-1)*(((c2_10 y z w a b)*(c3_2 y z w a b))+((c2_11 y z w a b)*(c3_1 y z w a b)))))+((-1)*(((c4_10 y z w a b)*(c5_2 y z w a b))+(((c4_11 y z w a b)*(c5_1 y z w a b))+(((c4_12 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c8_9 y z w a b)*(c9_3 y z w a b))+((c8_10 y z w a b)*(c9_2 y z w a b))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_6,c0_7,c0_8,c1_4,c1_5,c1_6,c2_10,c2_11,c3_1,c3_2,c4_10,c4_11,c4_12,c5_0,c5_1,c5_2,c8_10,c8_9,c9_2,c9_3]
  ring
#print axioms coefficient_12
theorem coefficient_13 (y z w a b : ℂ) : (certificate y z w a b)[13]?=some 0 := by
  change some (((((((c0_7 y z w a b)*(c1_6 y z w a b))+((c0_8 y z w a b)*(c1_5 y z w a b)))+((-1)*((c2_11 y z w a b)*(c3_2 y z w a b))))+((-1)*(((c4_11 y z w a b)*(c5_2 y z w a b))+((c4_12 y z w a b)*(c5_1 y z w a b)))))+((-1)*((c8_10 y z w a b)*(c9_3 y z w a b)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_7,c0_8,c1_5,c1_6,c2_11,c3_2,c4_11,c4_12,c5_1,c5_2,c8_10,c9_3]
  ring
#print axioms coefficient_13

theorem coefficient_14 (y z w a b : ℂ) : (certificate y z w a b)[14]?=some 0 := by
  change some ((((c0_8 y z w a b)*(c1_6 y z w a b))+((-1)*((c4_12 y z w a b)*(c5_2 y z w a b)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_8,c1_6,c4_12,c5_2]
  ring
#print axioms coefficient_14

end SmallLevelTwentySixMMPPariSyzygy6Column3
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariSyzygy6Column4
open SmallLevelPolynomialCoefficientCertificate

theorem coefficient_0 (y z w a b : ℂ) : (certificate y z w a b)[0]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_0 y z w a b))+0)+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_0 y z w a b))+0)))+((-1)*(((c8_0 y z w a b)*(c9_0 y z w a b))+0))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c1_0,c6_0,c7_0,c8_0,c9_0]
  ring
#print axioms coefficient_0
theorem coefficient_1 (y z w a b : ℂ) : (certificate y z w a b)[1]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_1 y z w a b))+(((c0_1 y z w a b)*(c1_0 y z w a b))+0))+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_1 y z w a b))+(((c6_1 y z w a b)*(c7_0 y z w a b))+0))))+((-1)*(((c8_0 y z w a b)*(c9_1 y z w a b))+(((c8_1 y z w a b)*(c9_0 y z w a b))+0)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c1_0,c1_1,c6_0,c6_1,c7_0,c7_1,c8_0,c8_1,c9_0,c9_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (y z w a b : ℂ) : (certificate y z w a b)[2]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_2 y z w a b))+(((c0_1 y z w a b)*(c1_1 y z w a b))+(((c0_2 y z w a b)*(c1_0 y z w a b))+0)))+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_2 y z w a b))+(((c6_1 y z w a b)*(c7_1 y z w a b))+(((c6_2 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_2 y z w a b))+(((c8_1 y z w a b)*(c9_1 y z w a b))+(((c8_2 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c1_0,c1_1,c1_2,c6_0,c6_1,c6_2,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_2
theorem coefficient_3 (y z w a b : ℂ) : (certificate y z w a b)[3]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_3 y z w a b))+(((c0_1 y z w a b)*(c1_2 y z w a b))+(((c0_2 y z w a b)*(c1_1 y z w a b))+(((c0_3 y z w a b)*(c1_0 y z w a b))+0))))+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_3 y z w a b))+(((c6_1 y z w a b)*(c7_2 y z w a b))+(((c6_2 y z w a b)*(c7_1 y z w a b))+(((c6_3 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_1 y z w a b)*(c9_2 y z w a b))+(((c8_2 y z w a b)*(c9_1 y z w a b))+(((c8_3 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c1_0,c1_1,c1_2,c1_3,c6_0,c6_1,c6_2,c6_3,c7_0,c7_1,c7_2,c7_3,c8_1,c8_2,c8_3,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_3

theorem coefficient_4 (y z w a b : ℂ) : (certificate y z w a b)[4]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_4 y z w a b))+(((c0_1 y z w a b)*(c1_3 y z w a b))+(((c0_2 y z w a b)*(c1_2 y z w a b))+(((c0_3 y z w a b)*(c1_1 y z w a b))+(((c0_4 y z w a b)*(c1_0 y z w a b))+0)))))+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_4 y z w a b))+(((c6_1 y z w a b)*(c7_3 y z w a b))+(((c6_2 y z w a b)*(c7_2 y z w a b))+(((c6_3 y z w a b)*(c7_1 y z w a b))+(((c6_4 y z w a b)*(c7_0 y z w a b))+0)))))))+((-1)*(((c8_2 y z w a b)*(c9_2 y z w a b))+(((c8_3 y z w a b)*(c9_1 y z w a b))+(((c8_4 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_0,c1_1,c1_2,c1_3,c1_4,c6_0,c6_1,c6_2,c6_3,c6_4,c7_0,c7_1,c7_2,c7_3,c7_4,c8_2,c8_3,c8_4,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_4
theorem coefficient_5 (y z w a b : ℂ) : (certificate y z w a b)[5]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_5 y z w a b))+(((c0_1 y z w a b)*(c1_4 y z w a b))+(((c0_2 y z w a b)*(c1_3 y z w a b))+(((c0_3 y z w a b)*(c1_2 y z w a b))+(((c0_4 y z w a b)*(c1_1 y z w a b))+(((c0_5 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_1 y z w a b)*(c7_4 y z w a b))+(((c6_2 y z w a b)*(c7_3 y z w a b))+(((c6_3 y z w a b)*(c7_2 y z w a b))+(((c6_4 y z w a b)*(c7_1 y z w a b))+(((c6_5 y z w a b)*(c7_0 y z w a b))+0)))))))+((-1)*(((c8_3 y z w a b)*(c9_2 y z w a b))+(((c8_4 y z w a b)*(c9_1 y z w a b))+(((c8_5 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c6_1,c6_2,c6_3,c6_4,c6_5,c7_0,c7_1,c7_2,c7_3,c7_4,c8_3,c8_4,c8_5,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_5

theorem coefficient_6 (y z w a b : ℂ) : (certificate y z w a b)[6]?=some 0 := by
  change some ((((((((c0_1 y z w a b)*(c1_5 y z w a b))+(((c0_2 y z w a b)*(c1_4 y z w a b))+(((c0_3 y z w a b)*(c1_3 y z w a b))+(((c0_4 y z w a b)*(c1_2 y z w a b))+(((c0_5 y z w a b)*(c1_1 y z w a b))+(((c0_6 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_2 y z w a b)*(c7_4 y z w a b))+(((c6_3 y z w a b)*(c7_3 y z w a b))+(((c6_4 y z w a b)*(c7_2 y z w a b))+(((c6_5 y z w a b)*(c7_1 y z w a b))+(((c6_6 y z w a b)*(c7_0 y z w a b))+0)))))))+((-1)*(((c8_4 y z w a b)*(c9_2 y z w a b))+(((c8_5 y z w a b)*(c9_1 y z w a b))+(((c8_6 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c6_2,c6_3,c6_4,c6_5,c6_6,c7_0,c7_1,c7_2,c7_3,c7_4,c8_4,c8_5,c8_6,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_6
theorem coefficient_7 (y z w a b : ℂ) : (certificate y z w a b)[7]?=some 0 := by
  change some ((((((((c0_2 y z w a b)*(c1_5 y z w a b))+(((c0_3 y z w a b)*(c1_4 y z w a b))+(((c0_4 y z w a b)*(c1_3 y z w a b))+(((c0_5 y z w a b)*(c1_2 y z w a b))+(((c0_6 y z w a b)*(c1_1 y z w a b))+(((c0_7 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_3 y z w a b)*(c7_4 y z w a b))+(((c6_4 y z w a b)*(c7_3 y z w a b))+(((c6_5 y z w a b)*(c7_2 y z w a b))+(((c6_6 y z w a b)*(c7_1 y z w a b))+(((c6_7 y z w a b)*(c7_0 y z w a b))+0)))))))+((-1)*(((c8_5 y z w a b)*(c9_2 y z w a b))+(((c8_6 y z w a b)*(c9_1 y z w a b))+(((c8_7 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c6_3,c6_4,c6_5,c6_6,c6_7,c7_0,c7_1,c7_2,c7_3,c7_4,c8_5,c8_6,c8_7,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_7

theorem coefficient_8 (y z w a b : ℂ) : (certificate y z w a b)[8]?=some 0 := by
  change some ((((((((c0_3 y z w a b)*(c1_5 y z w a b))+(((c0_4 y z w a b)*(c1_4 y z w a b))+(((c0_5 y z w a b)*(c1_3 y z w a b))+(((c0_6 y z w a b)*(c1_2 y z w a b))+(((c0_7 y z w a b)*(c1_1 y z w a b))+(((c0_8 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_4 y z w a b)*(c7_4 y z w a b))+(((c6_5 y z w a b)*(c7_3 y z w a b))+(((c6_6 y z w a b)*(c7_2 y z w a b))+(((c6_7 y z w a b)*(c7_1 y z w a b))+(((c6_8 y z w a b)*(c7_0 y z w a b))+0)))))))+((-1)*(((c8_6 y z w a b)*(c9_2 y z w a b))+(((c8_7 y z w a b)*(c9_1 y z w a b))+(((c8_8 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c6_4,c6_5,c6_6,c6_7,c6_8,c7_0,c7_1,c7_2,c7_3,c7_4,c8_6,c8_7,c8_8,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_8
theorem coefficient_9 (y z w a b : ℂ) : (certificate y z w a b)[9]?=some 0 := by
  change some ((((((((c0_4 y z w a b)*(c1_5 y z w a b))+(((c0_5 y z w a b)*(c1_4 y z w a b))+(((c0_6 y z w a b)*(c1_3 y z w a b))+(((c0_7 y z w a b)*(c1_2 y z w a b))+((c0_8 y z w a b)*(c1_1 y z w a b))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_5 y z w a b)*(c7_4 y z w a b))+(((c6_6 y z w a b)*(c7_3 y z w a b))+(((c6_7 y z w a b)*(c7_2 y z w a b))+(((c6_8 y z w a b)*(c7_1 y z w a b))+(((c6_9 y z w a b)*(c7_0 y z w a b))+0)))))))+((-1)*(((c8_7 y z w a b)*(c9_2 y z w a b))+(((c8_8 y z w a b)*(c9_1 y z w a b))+(((c8_9 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_4,c0_5,c0_6,c0_7,c0_8,c1_1,c1_2,c1_3,c1_4,c1_5,c6_5,c6_6,c6_7,c6_8,c6_9,c7_0,c7_1,c7_2,c7_3,c7_4,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_9

theorem coefficient_10 (y z w a b : ℂ) : (certificate y z w a b)[10]?=some 0 := by
  change some ((((((((c0_5 y z w a b)*(c1_5 y z w a b))+(((c0_6 y z w a b)*(c1_4 y z w a b))+(((c0_7 y z w a b)*(c1_3 y z w a b))+((c0_8 y z w a b)*(c1_2 y z w a b)))))+((-1)*0))+((-1)*0))+((-1)*(((c6_6 y z w a b)*(c7_4 y z w a b))+(((c6_7 y z w a b)*(c7_3 y z w a b))+(((c6_8 y z w a b)*(c7_2 y z w a b))+((c6_9 y z w a b)*(c7_1 y z w a b)))))))+((-1)*(((c8_8 y z w a b)*(c9_2 y z w a b))+(((c8_9 y z w a b)*(c9_1 y z w a b))+(((c8_10 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_5,c0_6,c0_7,c0_8,c1_2,c1_3,c1_4,c1_5,c6_6,c6_7,c6_8,c6_9,c7_1,c7_2,c7_3,c7_4,c8_10,c8_8,c8_9,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_10
theorem coefficient_11 (y z w a b : ℂ) : (certificate y z w a b)[11]?=some 0 := by
  change some ((((((((c0_6 y z w a b)*(c1_5 y z w a b))+(((c0_7 y z w a b)*(c1_4 y z w a b))+((c0_8 y z w a b)*(c1_3 y z w a b))))+((-1)*0))+((-1)*0))+((-1)*(((c6_7 y z w a b)*(c7_4 y z w a b))+(((c6_8 y z w a b)*(c7_3 y z w a b))+((c6_9 y z w a b)*(c7_2 y z w a b))))))+((-1)*(((c8_9 y z w a b)*(c9_2 y z w a b))+((c8_10 y z w a b)*(c9_1 y z w a b))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_6,c0_7,c0_8,c1_3,c1_4,c1_5,c6_7,c6_8,c6_9,c7_2,c7_3,c7_4,c8_10,c8_9,c9_1,c9_2]
  ring
#print axioms coefficient_11

theorem coefficient_12 (y z w a b : ℂ) : (certificate y z w a b)[12]?=some 0 := by
  change some (((((((c0_7 y z w a b)*(c1_5 y z w a b))+((c0_8 y z w a b)*(c1_4 y z w a b)))+((-1)*0))+((-1)*(((c6_8 y z w a b)*(c7_4 y z w a b))+((c6_9 y z w a b)*(c7_3 y z w a b)))))+((-1)*((c8_10 y z w a b)*(c9_2 y z w a b)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_7,c0_8,c1_4,c1_5,c6_8,c6_9,c7_3,c7_4,c8_10,c9_2]
  ring
#print axioms coefficient_12
theorem coefficient_13 (y z w a b : ℂ) : (certificate y z w a b)[13]?=some 0 := by
  change some ((((c0_8 y z w a b)*(c1_5 y z w a b))+((-1)*((c6_9 y z w a b)*(c7_4 y z w a b)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_8,c1_5,c6_9,c7_4]
  ring
#print axioms coefficient_13

end SmallLevelTwentySixMMPPariSyzygy6Column4
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariSyzygy6Column5
open SmallLevelPolynomialCoefficientCertificate

theorem coefficient_0 (y z w a b : ℂ) : (certificate y z w a b)[0]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_0 y z w a b))+0)+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_0 y z w a b))+0)))+((-1)*(((c8_0 y z w a b)*(c9_0 y z w a b))+0))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c1_0,c6_0,c7_0,c8_0,c9_0]
  ring
#print axioms coefficient_0
theorem coefficient_1 (y z w a b : ℂ) : (certificate y z w a b)[1]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_1 y z w a b))+(((c0_1 y z w a b)*(c1_0 y z w a b))+0))+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_1 y z w a b))+(((c6_1 y z w a b)*(c7_0 y z w a b))+0))))+((-1)*(((c8_0 y z w a b)*(c9_1 y z w a b))+(((c8_1 y z w a b)*(c9_0 y z w a b))+0)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c1_0,c1_1,c6_0,c6_1,c7_0,c7_1,c8_0,c8_1,c9_0,c9_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (y z w a b : ℂ) : (certificate y z w a b)[2]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_2 y z w a b))+(((c0_1 y z w a b)*(c1_1 y z w a b))+(((c0_2 y z w a b)*(c1_0 y z w a b))+0)))+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_2 y z w a b))+(((c6_1 y z w a b)*(c7_1 y z w a b))+(((c6_2 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_2 y z w a b))+(((c8_1 y z w a b)*(c9_1 y z w a b))+(((c8_2 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c1_0,c1_1,c1_2,c6_0,c6_1,c6_2,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_2
theorem coefficient_3 (y z w a b : ℂ) : (certificate y z w a b)[3]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_3 y z w a b))+(((c0_1 y z w a b)*(c1_2 y z w a b))+(((c0_2 y z w a b)*(c1_1 y z w a b))+(((c0_3 y z w a b)*(c1_0 y z w a b))+0))))+((-1)*0))+((-1)*0))+((-1)*(((c6_1 y z w a b)*(c7_2 y z w a b))+(((c6_2 y z w a b)*(c7_1 y z w a b))+(((c6_3 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_3 y z w a b))+(((c8_1 y z w a b)*(c9_2 y z w a b))+(((c8_2 y z w a b)*(c9_1 y z w a b))+(((c8_3 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c1_0,c1_1,c1_2,c1_3,c6_1,c6_2,c6_3,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c8_3,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (y z w a b : ℂ) : (certificate y z w a b)[4]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_4 y z w a b))+(((c0_1 y z w a b)*(c1_3 y z w a b))+(((c0_2 y z w a b)*(c1_2 y z w a b))+(((c0_3 y z w a b)*(c1_1 y z w a b))+(((c0_4 y z w a b)*(c1_0 y z w a b))+0)))))+((-1)*0))+((-1)*0))+((-1)*(((c6_2 y z w a b)*(c7_2 y z w a b))+(((c6_3 y z w a b)*(c7_1 y z w a b))+(((c6_4 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_1 y z w a b)*(c9_3 y z w a b))+(((c8_2 y z w a b)*(c9_2 y z w a b))+(((c8_3 y z w a b)*(c9_1 y z w a b))+(((c8_4 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_0,c1_1,c1_2,c1_3,c1_4,c6_2,c6_3,c6_4,c7_0,c7_1,c7_2,c8_1,c8_2,c8_3,c8_4,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_4
theorem coefficient_5 (y z w a b : ℂ) : (certificate y z w a b)[5]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_5 y z w a b))+(((c0_1 y z w a b)*(c1_4 y z w a b))+(((c0_2 y z w a b)*(c1_3 y z w a b))+(((c0_3 y z w a b)*(c1_2 y z w a b))+(((c0_4 y z w a b)*(c1_1 y z w a b))+(((c0_5 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_3 y z w a b)*(c7_2 y z w a b))+(((c6_4 y z w a b)*(c7_1 y z w a b))+(((c6_5 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_2 y z w a b)*(c9_3 y z w a b))+(((c8_3 y z w a b)*(c9_2 y z w a b))+(((c8_4 y z w a b)*(c9_1 y z w a b))+(((c8_5 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c6_3,c6_4,c6_5,c7_0,c7_1,c7_2,c8_2,c8_3,c8_4,c8_5,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_5

theorem coefficient_6 (y z w a b : ℂ) : (certificate y z w a b)[6]?=some 0 := by
  change some ((((((((c0_1 y z w a b)*(c1_5 y z w a b))+(((c0_2 y z w a b)*(c1_4 y z w a b))+(((c0_3 y z w a b)*(c1_3 y z w a b))+(((c0_4 y z w a b)*(c1_2 y z w a b))+(((c0_5 y z w a b)*(c1_1 y z w a b))+(((c0_6 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_4 y z w a b)*(c7_2 y z w a b))+(((c6_5 y z w a b)*(c7_1 y z w a b))+(((c6_6 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_3 y z w a b)*(c9_3 y z w a b))+(((c8_4 y z w a b)*(c9_2 y z w a b))+(((c8_5 y z w a b)*(c9_1 y z w a b))+(((c8_6 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c6_4,c6_5,c6_6,c7_0,c7_1,c7_2,c8_3,c8_4,c8_5,c8_6,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_6
theorem coefficient_7 (y z w a b : ℂ) : (certificate y z w a b)[7]?=some 0 := by
  change some ((((((((c0_2 y z w a b)*(c1_5 y z w a b))+(((c0_3 y z w a b)*(c1_4 y z w a b))+(((c0_4 y z w a b)*(c1_3 y z w a b))+(((c0_5 y z w a b)*(c1_2 y z w a b))+(((c0_6 y z w a b)*(c1_1 y z w a b))+(((c0_7 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_5 y z w a b)*(c7_2 y z w a b))+(((c6_6 y z w a b)*(c7_1 y z w a b))+(((c6_7 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_4 y z w a b)*(c9_3 y z w a b))+(((c8_5 y z w a b)*(c9_2 y z w a b))+(((c8_6 y z w a b)*(c9_1 y z w a b))+(((c8_7 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c6_5,c6_6,c6_7,c7_0,c7_1,c7_2,c8_4,c8_5,c8_6,c8_7,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_7

theorem coefficient_8 (y z w a b : ℂ) : (certificate y z w a b)[8]?=some 0 := by
  change some ((((((((c0_3 y z w a b)*(c1_5 y z w a b))+(((c0_4 y z w a b)*(c1_4 y z w a b))+(((c0_5 y z w a b)*(c1_3 y z w a b))+(((c0_6 y z w a b)*(c1_2 y z w a b))+(((c0_7 y z w a b)*(c1_1 y z w a b))+(((c0_8 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_6 y z w a b)*(c7_2 y z w a b))+(((c6_7 y z w a b)*(c7_1 y z w a b))+(((c6_8 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_5 y z w a b)*(c9_3 y z w a b))+(((c8_6 y z w a b)*(c9_2 y z w a b))+(((c8_7 y z w a b)*(c9_1 y z w a b))+(((c8_8 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c6_6,c6_7,c6_8,c7_0,c7_1,c7_2,c8_5,c8_6,c8_7,c8_8,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_8
theorem coefficient_9 (y z w a b : ℂ) : (certificate y z w a b)[9]?=some 0 := by
  change some ((((((((c0_4 y z w a b)*(c1_5 y z w a b))+(((c0_5 y z w a b)*(c1_4 y z w a b))+(((c0_6 y z w a b)*(c1_3 y z w a b))+(((c0_7 y z w a b)*(c1_2 y z w a b))+((c0_8 y z w a b)*(c1_1 y z w a b))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_7 y z w a b)*(c7_2 y z w a b))+(((c6_8 y z w a b)*(c7_1 y z w a b))+(((c6_9 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_6 y z w a b)*(c9_3 y z w a b))+(((c8_7 y z w a b)*(c9_2 y z w a b))+(((c8_8 y z w a b)*(c9_1 y z w a b))+(((c8_9 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_4,c0_5,c0_6,c0_7,c0_8,c1_1,c1_2,c1_3,c1_4,c1_5,c6_7,c6_8,c6_9,c7_0,c7_1,c7_2,c8_6,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_9

theorem coefficient_10 (y z w a b : ℂ) : (certificate y z w a b)[10]?=some 0 := by
  change some ((((((((c0_5 y z w a b)*(c1_5 y z w a b))+(((c0_6 y z w a b)*(c1_4 y z w a b))+(((c0_7 y z w a b)*(c1_3 y z w a b))+((c0_8 y z w a b)*(c1_2 y z w a b)))))+((-1)*0))+((-1)*0))+((-1)*(((c6_8 y z w a b)*(c7_2 y z w a b))+((c6_9 y z w a b)*(c7_1 y z w a b)))))+((-1)*(((c8_7 y z w a b)*(c9_3 y z w a b))+(((c8_8 y z w a b)*(c9_2 y z w a b))+(((c8_9 y z w a b)*(c9_1 y z w a b))+(((c8_10 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_5,c0_6,c0_7,c0_8,c1_2,c1_3,c1_4,c1_5,c6_8,c6_9,c7_1,c7_2,c8_10,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_10
theorem coefficient_11 (y z w a b : ℂ) : (certificate y z w a b)[11]?=some 0 := by
  change some ((((((((c0_6 y z w a b)*(c1_5 y z w a b))+(((c0_7 y z w a b)*(c1_4 y z w a b))+((c0_8 y z w a b)*(c1_3 y z w a b))))+((-1)*0))+((-1)*0))+((-1)*((c6_9 y z w a b)*(c7_2 y z w a b))))+((-1)*(((c8_8 y z w a b)*(c9_3 y z w a b))+(((c8_9 y z w a b)*(c9_2 y z w a b))+((c8_10 y z w a b)*(c9_1 y z w a b)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_6,c0_7,c0_8,c1_3,c1_4,c1_5,c6_9,c7_2,c8_10,c8_8,c8_9,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_11

theorem coefficient_12 (y z w a b : ℂ) : (certificate y z w a b)[12]?=some 0 := by
  change some ((((((c0_7 y z w a b)*(c1_5 y z w a b))+((c0_8 y z w a b)*(c1_4 y z w a b)))+((-1)*0))+((-1)*(((c8_9 y z w a b)*(c9_3 y z w a b))+((c8_10 y z w a b)*(c9_2 y z w a b))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_7,c0_8,c1_4,c1_5,c8_10,c8_9,c9_2,c9_3]
  ring
#print axioms coefficient_12
theorem coefficient_13 (y z w a b : ℂ) : (certificate y z w a b)[13]?=some 0 := by
  change some ((((c0_8 y z w a b)*(c1_5 y z w a b))+((-1)*((c8_10 y z w a b)*(c9_3 y z w a b)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_8,c1_5,c8_10,c9_3]
  ring
#print axioms coefficient_13

end SmallLevelTwentySixMMPPariSyzygy6Column5
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariSyzygy7Column0
open SmallLevelPolynomialCoefficientCertificate

theorem coefficient_0 (y z w a b : ℂ) : (certificate y z w a b)[0]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_0 y z w a b))+0)+((-1)*(((c2_0 y z w a b)*(c3_0 y z w a b))+0)))+((-1)*(((c4_0 y z w a b)*(c5_0 y z w a b))+0)))+((-1)*(((c6_0 y z w a b)*(c7_0 y z w a b))+0)))+((-1)*(((c8_0 y z w a b)*(c9_0 y z w a b))+0)))+((-1)*(c10_0 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c10_0,c1_0,c2_0,c3_0,c4_0,c5_0,c6_0,c7_0,c8_0,c9_0]
  ring
#print axioms coefficient_0
theorem coefficient_1 (y z w a b : ℂ) : (certificate y z w a b)[1]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_1 y z w a b))+(((c0_1 y z w a b)*(c1_0 y z w a b))+0))+((-1)*(((c2_0 y z w a b)*(c3_1 y z w a b))+(((c2_1 y z w a b)*(c3_0 y z w a b))+0))))+((-1)*(((c4_0 y z w a b)*(c5_1 y z w a b))+(((c4_1 y z w a b)*(c5_0 y z w a b))+0))))+((-1)*(((c6_0 y z w a b)*(c7_1 y z w a b))+(((c6_1 y z w a b)*(c7_0 y z w a b))+0))))+((-1)*(((c8_0 y z w a b)*(c9_1 y z w a b))+(((c8_1 y z w a b)*(c9_0 y z w a b))+0))))+((-1)*(c10_1 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c10_1,c1_0,c1_1,c2_0,c2_1,c3_0,c3_1,c4_0,c4_1,c5_0,c5_1,c6_0,c6_1,c7_0,c7_1,c8_0,c8_1,c9_0,c9_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (y z w a b : ℂ) : (certificate y z w a b)[2]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_2 y z w a b))+(((c0_1 y z w a b)*(c1_1 y z w a b))+(((c0_2 y z w a b)*(c1_0 y z w a b))+0)))+((-1)*(((c2_0 y z w a b)*(c3_2 y z w a b))+(((c2_1 y z w a b)*(c3_1 y z w a b))+(((c2_2 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_0 y z w a b)*(c5_2 y z w a b))+(((c4_1 y z w a b)*(c5_1 y z w a b))+(((c4_2 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_0 y z w a b)*(c7_2 y z w a b))+(((c6_1 y z w a b)*(c7_1 y z w a b))+(((c6_2 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_2 y z w a b))+(((c8_1 y z w a b)*(c9_1 y z w a b))+(((c8_2 y z w a b)*(c9_0 y z w a b))+0)))))+((-1)*(c10_2 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c10_2,c1_0,c1_1,c1_2,c2_0,c2_1,c2_2,c3_0,c3_1,c3_2,c4_0,c4_1,c4_2,c5_0,c5_1,c5_2,c6_0,c6_1,c6_2,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_2
theorem coefficient_3 (y z w a b : ℂ) : (certificate y z w a b)[3]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_3 y z w a b))+(((c0_1 y z w a b)*(c1_2 y z w a b))+(((c0_2 y z w a b)*(c1_1 y z w a b))+(((c0_3 y z w a b)*(c1_0 y z w a b))+0))))+((-1)*(((c2_0 y z w a b)*(c3_3 y z w a b))+(((c2_1 y z w a b)*(c3_2 y z w a b))+(((c2_2 y z w a b)*(c3_1 y z w a b))+(((c2_3 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_0 y z w a b)*(c5_3 y z w a b))+(((c4_1 y z w a b)*(c5_2 y z w a b))+(((c4_2 y z w a b)*(c5_1 y z w a b))+(((c4_3 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_0 y z w a b)*(c7_3 y z w a b))+(((c6_1 y z w a b)*(c7_2 y z w a b))+(((c6_2 y z w a b)*(c7_1 y z w a b))+(((c6_3 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_0 y z w a b)*(c9_3 y z w a b))+(((c8_1 y z w a b)*(c9_2 y z w a b))+(((c8_2 y z w a b)*(c9_1 y z w a b))+(((c8_3 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_3 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c10_3,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c3_0,c3_1,c3_2,c3_3,c4_0,c4_1,c4_2,c4_3,c5_0,c5_1,c5_2,c5_3,c6_0,c6_1,c6_2,c6_3,c7_0,c7_1,c7_2,c7_3,c8_0,c8_1,c8_2,c8_3,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (y z w a b : ℂ) : (certificate y z w a b)[4]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_4 y z w a b))+(((c0_1 y z w a b)*(c1_3 y z w a b))+(((c0_2 y z w a b)*(c1_2 y z w a b))+(((c0_3 y z w a b)*(c1_1 y z w a b))+(((c0_4 y z w a b)*(c1_0 y z w a b))+0)))))+((-1)*(((c2_1 y z w a b)*(c3_3 y z w a b))+(((c2_2 y z w a b)*(c3_2 y z w a b))+(((c2_3 y z w a b)*(c3_1 y z w a b))+(((c2_4 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_1 y z w a b)*(c5_3 y z w a b))+(((c4_2 y z w a b)*(c5_2 y z w a b))+(((c4_3 y z w a b)*(c5_1 y z w a b))+(((c4_4 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_1 y z w a b)*(c7_3 y z w a b))+(((c6_2 y z w a b)*(c7_2 y z w a b))+(((c6_3 y z w a b)*(c7_1 y z w a b))+(((c6_4 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_0 y z w a b)*(c9_4 y z w a b))+(((c8_1 y z w a b)*(c9_3 y z w a b))+(((c8_2 y z w a b)*(c9_2 y z w a b))+(((c8_3 y z w a b)*(c9_1 y z w a b))+(((c8_4 y z w a b)*(c9_0 y z w a b))+0)))))))+((-1)*(c10_4 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c10_4,c1_0,c1_1,c1_2,c1_3,c1_4,c2_1,c2_2,c2_3,c2_4,c3_0,c3_1,c3_2,c3_3,c4_1,c4_2,c4_3,c4_4,c5_0,c5_1,c5_2,c5_3,c6_1,c6_2,c6_3,c6_4,c7_0,c7_1,c7_2,c7_3,c8_0,c8_1,c8_2,c8_3,c8_4,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_4
theorem coefficient_5 (y z w a b : ℂ) : (certificate y z w a b)[5]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_5 y z w a b))+(((c0_1 y z w a b)*(c1_4 y z w a b))+(((c0_2 y z w a b)*(c1_3 y z w a b))+(((c0_3 y z w a b)*(c1_2 y z w a b))+(((c0_4 y z w a b)*(c1_1 y z w a b))+(((c0_5 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*(((c2_2 y z w a b)*(c3_3 y z w a b))+(((c2_3 y z w a b)*(c3_2 y z w a b))+(((c2_4 y z w a b)*(c3_1 y z w a b))+(((c2_5 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_2 y z w a b)*(c5_3 y z w a b))+(((c4_3 y z w a b)*(c5_2 y z w a b))+(((c4_4 y z w a b)*(c5_1 y z w a b))+(((c4_5 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_2 y z w a b)*(c7_3 y z w a b))+(((c6_3 y z w a b)*(c7_2 y z w a b))+(((c6_4 y z w a b)*(c7_1 y z w a b))+(((c6_5 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_1 y z w a b)*(c9_4 y z w a b))+(((c8_2 y z w a b)*(c9_3 y z w a b))+(((c8_3 y z w a b)*(c9_2 y z w a b))+(((c8_4 y z w a b)*(c9_1 y z w a b))+(((c8_5 y z w a b)*(c9_0 y z w a b))+0)))))))+((-1)*(c10_5 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c10_5,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_2,c2_3,c2_4,c2_5,c3_0,c3_1,c3_2,c3_3,c4_2,c4_3,c4_4,c4_5,c5_0,c5_1,c5_2,c5_3,c6_2,c6_3,c6_4,c6_5,c7_0,c7_1,c7_2,c7_3,c8_1,c8_2,c8_3,c8_4,c8_5,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_5

theorem coefficient_6 (y z w a b : ℂ) : (certificate y z w a b)[6]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_6 y z w a b))+(((c0_1 y z w a b)*(c1_5 y z w a b))+(((c0_2 y z w a b)*(c1_4 y z w a b))+(((c0_3 y z w a b)*(c1_3 y z w a b))+(((c0_4 y z w a b)*(c1_2 y z w a b))+(((c0_5 y z w a b)*(c1_1 y z w a b))+(((c0_6 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*(((c2_3 y z w a b)*(c3_3 y z w a b))+(((c2_4 y z w a b)*(c3_2 y z w a b))+(((c2_5 y z w a b)*(c3_1 y z w a b))+(((c2_6 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_3 y z w a b)*(c5_3 y z w a b))+(((c4_4 y z w a b)*(c5_2 y z w a b))+(((c4_5 y z w a b)*(c5_1 y z w a b))+(((c4_6 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_3 y z w a b)*(c7_3 y z w a b))+(((c6_4 y z w a b)*(c7_2 y z w a b))+(((c6_5 y z w a b)*(c7_1 y z w a b))+(((c6_6 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_2 y z w a b)*(c9_4 y z w a b))+(((c8_3 y z w a b)*(c9_3 y z w a b))+(((c8_4 y z w a b)*(c9_2 y z w a b))+(((c8_5 y z w a b)*(c9_1 y z w a b))+(((c8_6 y z w a b)*(c9_0 y z w a b))+0)))))))+((-1)*(c10_6 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c10_6,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_3,c2_4,c2_5,c2_6,c3_0,c3_1,c3_2,c3_3,c4_3,c4_4,c4_5,c4_6,c5_0,c5_1,c5_2,c5_3,c6_3,c6_4,c6_5,c6_6,c7_0,c7_1,c7_2,c7_3,c8_2,c8_3,c8_4,c8_5,c8_6,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_6
theorem coefficient_7 (y z w a b : ℂ) : (certificate y z w a b)[7]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_7 y z w a b))+(((c0_1 y z w a b)*(c1_6 y z w a b))+(((c0_2 y z w a b)*(c1_5 y z w a b))+(((c0_3 y z w a b)*(c1_4 y z w a b))+(((c0_4 y z w a b)*(c1_3 y z w a b))+(((c0_5 y z w a b)*(c1_2 y z w a b))+(((c0_6 y z w a b)*(c1_1 y z w a b))+(((c0_7 y z w a b)*(c1_0 y z w a b))+0))))))))+((-1)*(((c2_4 y z w a b)*(c3_3 y z w a b))+(((c2_5 y z w a b)*(c3_2 y z w a b))+(((c2_6 y z w a b)*(c3_1 y z w a b))+(((c2_7 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_4 y z w a b)*(c5_3 y z w a b))+(((c4_5 y z w a b)*(c5_2 y z w a b))+(((c4_6 y z w a b)*(c5_1 y z w a b))+(((c4_7 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_4 y z w a b)*(c7_3 y z w a b))+(((c6_5 y z w a b)*(c7_2 y z w a b))+(((c6_6 y z w a b)*(c7_1 y z w a b))+(((c6_7 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_3 y z w a b)*(c9_4 y z w a b))+(((c8_4 y z w a b)*(c9_3 y z w a b))+(((c8_5 y z w a b)*(c9_2 y z w a b))+(((c8_6 y z w a b)*(c9_1 y z w a b))+(((c8_7 y z w a b)*(c9_0 y z w a b))+0)))))))+((-1)*(c10_7 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c10_7,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c2_4,c2_5,c2_6,c2_7,c3_0,c3_1,c3_2,c3_3,c4_4,c4_5,c4_6,c4_7,c5_0,c5_1,c5_2,c5_3,c6_4,c6_5,c6_6,c6_7,c7_0,c7_1,c7_2,c7_3,c8_3,c8_4,c8_5,c8_6,c8_7,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_7

theorem coefficient_8 (y z w a b : ℂ) : (certificate y z w a b)[8]?=some 0 := by
  change some (((((((((c0_1 y z w a b)*(c1_7 y z w a b))+(((c0_2 y z w a b)*(c1_6 y z w a b))+(((c0_3 y z w a b)*(c1_5 y z w a b))+(((c0_4 y z w a b)*(c1_4 y z w a b))+(((c0_5 y z w a b)*(c1_3 y z w a b))+(((c0_6 y z w a b)*(c1_2 y z w a b))+(((c0_7 y z w a b)*(c1_1 y z w a b))+(((c0_8 y z w a b)*(c1_0 y z w a b))+0))))))))+((-1)*(((c2_5 y z w a b)*(c3_3 y z w a b))+(((c2_6 y z w a b)*(c3_2 y z w a b))+(((c2_7 y z w a b)*(c3_1 y z w a b))+(((c2_8 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_5 y z w a b)*(c5_3 y z w a b))+(((c4_6 y z w a b)*(c5_2 y z w a b))+(((c4_7 y z w a b)*(c5_1 y z w a b))+(((c4_8 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_5 y z w a b)*(c7_3 y z w a b))+(((c6_6 y z w a b)*(c7_2 y z w a b))+(((c6_7 y z w a b)*(c7_1 y z w a b))+(((c6_8 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_4 y z w a b)*(c9_4 y z w a b))+(((c8_5 y z w a b)*(c9_3 y z w a b))+(((c8_6 y z w a b)*(c9_2 y z w a b))+(((c8_7 y z w a b)*(c9_1 y z w a b))+(((c8_8 y z w a b)*(c9_0 y z w a b))+0)))))))+((-1)*(c10_8 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c10_8,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c2_5,c2_6,c2_7,c2_8,c3_0,c3_1,c3_2,c3_3,c4_5,c4_6,c4_7,c4_8,c5_0,c5_1,c5_2,c5_3,c6_5,c6_6,c6_7,c6_8,c7_0,c7_1,c7_2,c7_3,c8_4,c8_5,c8_6,c8_7,c8_8,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_8
theorem coefficient_9 (y z w a b : ℂ) : (certificate y z w a b)[9]?=some 0 := by
  change some (((((((((c0_2 y z w a b)*(c1_7 y z w a b))+(((c0_3 y z w a b)*(c1_6 y z w a b))+(((c0_4 y z w a b)*(c1_5 y z w a b))+(((c0_5 y z w a b)*(c1_4 y z w a b))+(((c0_6 y z w a b)*(c1_3 y z w a b))+(((c0_7 y z w a b)*(c1_2 y z w a b))+((c0_8 y z w a b)*(c1_1 y z w a b))))))))+((-1)*(((c2_6 y z w a b)*(c3_3 y z w a b))+(((c2_7 y z w a b)*(c3_2 y z w a b))+(((c2_8 y z w a b)*(c3_1 y z w a b))+(((c2_9 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_6 y z w a b)*(c5_3 y z w a b))+(((c4_7 y z w a b)*(c5_2 y z w a b))+(((c4_8 y z w a b)*(c5_1 y z w a b))+(((c4_9 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_6 y z w a b)*(c7_3 y z w a b))+(((c6_7 y z w a b)*(c7_2 y z w a b))+(((c6_8 y z w a b)*(c7_1 y z w a b))+(((c6_9 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_5 y z w a b)*(c9_4 y z w a b))+(((c8_6 y z w a b)*(c9_3 y z w a b))+(((c8_7 y z w a b)*(c9_2 y z w a b))+(((c8_8 y z w a b)*(c9_1 y z w a b))+(((c8_9 y z w a b)*(c9_0 y z w a b))+0)))))))+((-1)*(c10_9 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c10_9,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_2,c3_3,c4_6,c4_7,c4_8,c4_9,c5_0,c5_1,c5_2,c5_3,c6_6,c6_7,c6_8,c6_9,c7_0,c7_1,c7_2,c7_3,c8_5,c8_6,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_9

theorem coefficient_10 (y z w a b : ℂ) : (certificate y z w a b)[10]?=some 0 := by
  change some (((((((((c0_3 y z w a b)*(c1_7 y z w a b))+(((c0_4 y z w a b)*(c1_6 y z w a b))+(((c0_5 y z w a b)*(c1_5 y z w a b))+(((c0_6 y z w a b)*(c1_4 y z w a b))+(((c0_7 y z w a b)*(c1_3 y z w a b))+((c0_8 y z w a b)*(c1_2 y z w a b)))))))+((-1)*(((c2_7 y z w a b)*(c3_3 y z w a b))+(((c2_8 y z w a b)*(c3_2 y z w a b))+(((c2_9 y z w a b)*(c3_1 y z w a b))+(((c2_10 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_7 y z w a b)*(c5_3 y z w a b))+(((c4_8 y z w a b)*(c5_2 y z w a b))+(((c4_9 y z w a b)*(c5_1 y z w a b))+(((c4_10 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_7 y z w a b)*(c7_3 y z w a b))+(((c6_8 y z w a b)*(c7_2 y z w a b))+((c6_9 y z w a b)*(c7_1 y z w a b))))))+((-1)*(((c8_6 y z w a b)*(c9_4 y z w a b))+(((c8_7 y z w a b)*(c9_3 y z w a b))+(((c8_8 y z w a b)*(c9_2 y z w a b))+(((c8_9 y z w a b)*(c9_1 y z w a b))+(((c8_10 y z w a b)*(c9_0 y z w a b))+0)))))))+((-1)*(c10_10 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c10_10,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c2_10,c2_7,c2_8,c2_9,c3_0,c3_1,c3_2,c3_3,c4_10,c4_7,c4_8,c4_9,c5_0,c5_1,c5_2,c5_3,c6_7,c6_8,c6_9,c7_1,c7_2,c7_3,c8_10,c8_6,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_10
theorem coefficient_11 (y z w a b : ℂ) : (certificate y z w a b)[11]?=some 0 := by
  change some (((((((((c0_4 y z w a b)*(c1_7 y z w a b))+(((c0_5 y z w a b)*(c1_6 y z w a b))+(((c0_6 y z w a b)*(c1_5 y z w a b))+(((c0_7 y z w a b)*(c1_4 y z w a b))+((c0_8 y z w a b)*(c1_3 y z w a b))))))+((-1)*(((c2_8 y z w a b)*(c3_3 y z w a b))+(((c2_9 y z w a b)*(c3_2 y z w a b))+(((c2_10 y z w a b)*(c3_1 y z w a b))+(((c2_11 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_8 y z w a b)*(c5_3 y z w a b))+(((c4_9 y z w a b)*(c5_2 y z w a b))+(((c4_10 y z w a b)*(c5_1 y z w a b))+(((c4_11 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_8 y z w a b)*(c7_3 y z w a b))+((c6_9 y z w a b)*(c7_2 y z w a b)))))+((-1)*(((c8_7 y z w a b)*(c9_4 y z w a b))+(((c8_8 y z w a b)*(c9_3 y z w a b))+(((c8_9 y z w a b)*(c9_2 y z w a b))+(((c8_10 y z w a b)*(c9_1 y z w a b))+(((c8_11 y z w a b)*(c9_0 y z w a b))+0)))))))+((-1)*(c10_11 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_4,c0_5,c0_6,c0_7,c0_8,c10_11,c1_3,c1_4,c1_5,c1_6,c1_7,c2_10,c2_11,c2_8,c2_9,c3_0,c3_1,c3_2,c3_3,c4_10,c4_11,c4_8,c4_9,c5_0,c5_1,c5_2,c5_3,c6_8,c6_9,c7_2,c7_3,c8_10,c8_11,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_11

theorem coefficient_12 (y z w a b : ℂ) : (certificate y z w a b)[12]?=some 0 := by
  change some (((((((((c0_5 y z w a b)*(c1_7 y z w a b))+(((c0_6 y z w a b)*(c1_6 y z w a b))+(((c0_7 y z w a b)*(c1_5 y z w a b))+((c0_8 y z w a b)*(c1_4 y z w a b)))))+((-1)*(((c2_9 y z w a b)*(c3_3 y z w a b))+(((c2_10 y z w a b)*(c3_2 y z w a b))+((c2_11 y z w a b)*(c3_1 y z w a b))))))+((-1)*(((c4_9 y z w a b)*(c5_3 y z w a b))+(((c4_10 y z w a b)*(c5_2 y z w a b))+((c4_11 y z w a b)*(c5_1 y z w a b))))))+((-1)*((c6_9 y z w a b)*(c7_3 y z w a b))))+((-1)*(((c8_8 y z w a b)*(c9_4 y z w a b))+(((c8_9 y z w a b)*(c9_3 y z w a b))+(((c8_10 y z w a b)*(c9_2 y z w a b))+((c8_11 y z w a b)*(c9_1 y z w a b)))))))+((-1)*(c10_12 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_5,c0_6,c0_7,c0_8,c10_12,c1_4,c1_5,c1_6,c1_7,c2_10,c2_11,c2_9,c3_1,c3_2,c3_3,c4_10,c4_11,c4_9,c5_1,c5_2,c5_3,c6_9,c7_3,c8_10,c8_11,c8_8,c8_9,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_12
theorem coefficient_13 (y z w a b : ℂ) : (certificate y z w a b)[13]?=some 0 := by
  change some ((((((((c0_6 y z w a b)*(c1_7 y z w a b))+(((c0_7 y z w a b)*(c1_6 y z w a b))+((c0_8 y z w a b)*(c1_5 y z w a b))))+((-1)*(((c2_10 y z w a b)*(c3_3 y z w a b))+((c2_11 y z w a b)*(c3_2 y z w a b)))))+((-1)*(((c4_10 y z w a b)*(c5_3 y z w a b))+((c4_11 y z w a b)*(c5_2 y z w a b)))))+((-1)*(((c8_9 y z w a b)*(c9_4 y z w a b))+(((c8_10 y z w a b)*(c9_3 y z w a b))+((c8_11 y z w a b)*(c9_2 y z w a b))))))+((-1)*(c10_13 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_6,c0_7,c0_8,c10_13,c1_5,c1_6,c1_7,c2_10,c2_11,c3_2,c3_3,c4_10,c4_11,c5_2,c5_3,c8_10,c8_11,c8_9,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_13

theorem coefficient_14 (y z w a b : ℂ) : (certificate y z w a b)[14]?=some 0 := by
  change some ((((((((c0_7 y z w a b)*(c1_7 y z w a b))+((c0_8 y z w a b)*(c1_6 y z w a b)))+((-1)*((c2_11 y z w a b)*(c3_3 y z w a b))))+((-1)*((c4_11 y z w a b)*(c5_3 y z w a b))))+((-1)*(((c8_10 y z w a b)*(c9_4 y z w a b))+((c8_11 y z w a b)*(c9_3 y z w a b)))))+((-1)*(c10_14 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_7,c0_8,c10_14,c1_6,c1_7,c2_11,c3_3,c4_11,c5_3,c8_10,c8_11,c9_3,c9_4]
  ring
#print axioms coefficient_14
theorem coefficient_15 (y z w a b : ℂ) : (certificate y z w a b)[15]?=some 0 := by
  change some ((((c0_8 y z w a b)*(c1_7 y z w a b))+((-1)*((c8_11 y z w a b)*(c9_4 y z w a b)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_8,c1_7,c8_11,c9_4]
  ring
#print axioms coefficient_15

end SmallLevelTwentySixMMPPariSyzygy7Column0
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariSyzygy7Column1
open SmallLevelPolynomialCoefficientCertificate

theorem coefficient_0 (y z w a b : ℂ) : (certificate y z w a b)[0]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_0 y z w a b))+0)+((-1)*(((c2_0 y z w a b)*(c3_0 y z w a b))+0)))+((-1)*(((c4_0 y z w a b)*(c5_0 y z w a b))+0)))+((-1)*(((c6_0 y z w a b)*(c7_0 y z w a b))+0)))+((-1)*(((c8_0 y z w a b)*(c9_0 y z w a b))+0)))+((-1)*(c10_0 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c10_0,c1_0,c2_0,c3_0,c4_0,c5_0,c6_0,c7_0,c8_0,c9_0]
  ring
#print axioms coefficient_0
theorem coefficient_1 (y z w a b : ℂ) : (certificate y z w a b)[1]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_1 y z w a b))+(((c0_1 y z w a b)*(c1_0 y z w a b))+0))+((-1)*(((c2_0 y z w a b)*(c3_1 y z w a b))+(((c2_1 y z w a b)*(c3_0 y z w a b))+0))))+((-1)*(((c4_0 y z w a b)*(c5_1 y z w a b))+(((c4_1 y z w a b)*(c5_0 y z w a b))+0))))+((-1)*(((c6_0 y z w a b)*(c7_1 y z w a b))+(((c6_1 y z w a b)*(c7_0 y z w a b))+0))))+((-1)*(((c8_0 y z w a b)*(c9_1 y z w a b))+(((c8_1 y z w a b)*(c9_0 y z w a b))+0))))+((-1)*(c10_1 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c10_1,c1_0,c1_1,c2_0,c2_1,c3_0,c3_1,c4_0,c4_1,c5_0,c5_1,c6_0,c6_1,c7_0,c7_1,c8_0,c8_1,c9_0,c9_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (y z w a b : ℂ) : (certificate y z w a b)[2]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_2 y z w a b))+(((c0_1 y z w a b)*(c1_1 y z w a b))+(((c0_2 y z w a b)*(c1_0 y z w a b))+0)))+((-1)*(((c2_0 y z w a b)*(c3_2 y z w a b))+(((c2_1 y z w a b)*(c3_1 y z w a b))+(((c2_2 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_0 y z w a b)*(c5_2 y z w a b))+(((c4_1 y z w a b)*(c5_1 y z w a b))+(((c4_2 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_0 y z w a b)*(c7_2 y z w a b))+(((c6_1 y z w a b)*(c7_1 y z w a b))+(((c6_2 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_2 y z w a b))+(((c8_1 y z w a b)*(c9_1 y z w a b))+(((c8_2 y z w a b)*(c9_0 y z w a b))+0)))))+((-1)*(c10_2 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c10_2,c1_0,c1_1,c1_2,c2_0,c2_1,c2_2,c3_0,c3_1,c3_2,c4_0,c4_1,c4_2,c5_0,c5_1,c5_2,c6_0,c6_1,c6_2,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_2
theorem coefficient_3 (y z w a b : ℂ) : (certificate y z w a b)[3]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_3 y z w a b))+(((c0_1 y z w a b)*(c1_2 y z w a b))+(((c0_2 y z w a b)*(c1_1 y z w a b))+(((c0_3 y z w a b)*(c1_0 y z w a b))+0))))+((-1)*(((c2_1 y z w a b)*(c3_2 y z w a b))+(((c2_2 y z w a b)*(c3_1 y z w a b))+(((c2_3 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_1 y z w a b)*(c5_2 y z w a b))+(((c4_2 y z w a b)*(c5_1 y z w a b))+(((c4_3 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_1 y z w a b)*(c7_2 y z w a b))+(((c6_2 y z w a b)*(c7_1 y z w a b))+(((c6_3 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_3 y z w a b))+(((c8_1 y z w a b)*(c9_2 y z w a b))+(((c8_2 y z w a b)*(c9_1 y z w a b))+(((c8_3 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_3 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c10_3,c1_0,c1_1,c1_2,c1_3,c2_1,c2_2,c2_3,c3_0,c3_1,c3_2,c4_1,c4_2,c4_3,c5_0,c5_1,c5_2,c6_1,c6_2,c6_3,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c8_3,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (y z w a b : ℂ) : (certificate y z w a b)[4]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_4 y z w a b))+(((c0_1 y z w a b)*(c1_3 y z w a b))+(((c0_2 y z w a b)*(c1_2 y z w a b))+(((c0_3 y z w a b)*(c1_1 y z w a b))+(((c0_4 y z w a b)*(c1_0 y z w a b))+0)))))+((-1)*(((c2_2 y z w a b)*(c3_2 y z w a b))+(((c2_3 y z w a b)*(c3_1 y z w a b))+(((c2_4 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_2 y z w a b)*(c5_2 y z w a b))+(((c4_3 y z w a b)*(c5_1 y z w a b))+(((c4_4 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_2 y z w a b)*(c7_2 y z w a b))+(((c6_3 y z w a b)*(c7_1 y z w a b))+(((c6_4 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_1 y z w a b)*(c9_3 y z w a b))+(((c8_2 y z w a b)*(c9_2 y z w a b))+(((c8_3 y z w a b)*(c9_1 y z w a b))+(((c8_4 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_4 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c10_4,c1_0,c1_1,c1_2,c1_3,c1_4,c2_2,c2_3,c2_4,c3_0,c3_1,c3_2,c4_2,c4_3,c4_4,c5_0,c5_1,c5_2,c6_2,c6_3,c6_4,c7_0,c7_1,c7_2,c8_1,c8_2,c8_3,c8_4,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_4
theorem coefficient_5 (y z w a b : ℂ) : (certificate y z w a b)[5]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_5 y z w a b))+(((c0_1 y z w a b)*(c1_4 y z w a b))+(((c0_2 y z w a b)*(c1_3 y z w a b))+(((c0_3 y z w a b)*(c1_2 y z w a b))+(((c0_4 y z w a b)*(c1_1 y z w a b))+(((c0_5 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*(((c2_3 y z w a b)*(c3_2 y z w a b))+(((c2_4 y z w a b)*(c3_1 y z w a b))+(((c2_5 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_3 y z w a b)*(c5_2 y z w a b))+(((c4_4 y z w a b)*(c5_1 y z w a b))+(((c4_5 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_3 y z w a b)*(c7_2 y z w a b))+(((c6_4 y z w a b)*(c7_1 y z w a b))+(((c6_5 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_2 y z w a b)*(c9_3 y z w a b))+(((c8_3 y z w a b)*(c9_2 y z w a b))+(((c8_4 y z w a b)*(c9_1 y z w a b))+(((c8_5 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_5 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c10_5,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_3,c2_4,c2_5,c3_0,c3_1,c3_2,c4_3,c4_4,c4_5,c5_0,c5_1,c5_2,c6_3,c6_4,c6_5,c7_0,c7_1,c7_2,c8_2,c8_3,c8_4,c8_5,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_5

theorem coefficient_6 (y z w a b : ℂ) : (certificate y z w a b)[6]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_6 y z w a b))+(((c0_1 y z w a b)*(c1_5 y z w a b))+(((c0_2 y z w a b)*(c1_4 y z w a b))+(((c0_3 y z w a b)*(c1_3 y z w a b))+(((c0_4 y z w a b)*(c1_2 y z w a b))+(((c0_5 y z w a b)*(c1_1 y z w a b))+(((c0_6 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*(((c2_4 y z w a b)*(c3_2 y z w a b))+(((c2_5 y z w a b)*(c3_1 y z w a b))+(((c2_6 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_4 y z w a b)*(c5_2 y z w a b))+(((c4_5 y z w a b)*(c5_1 y z w a b))+(((c4_6 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_4 y z w a b)*(c7_2 y z w a b))+(((c6_5 y z w a b)*(c7_1 y z w a b))+(((c6_6 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_3 y z w a b)*(c9_3 y z w a b))+(((c8_4 y z w a b)*(c9_2 y z w a b))+(((c8_5 y z w a b)*(c9_1 y z w a b))+(((c8_6 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_6 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c10_6,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_4,c2_5,c2_6,c3_0,c3_1,c3_2,c4_4,c4_5,c4_6,c5_0,c5_1,c5_2,c6_4,c6_5,c6_6,c7_0,c7_1,c7_2,c8_3,c8_4,c8_5,c8_6,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_6
theorem coefficient_7 (y z w a b : ℂ) : (certificate y z w a b)[7]?=some 0 := by
  change some (((((((((c0_1 y z w a b)*(c1_6 y z w a b))+(((c0_2 y z w a b)*(c1_5 y z w a b))+(((c0_3 y z w a b)*(c1_4 y z w a b))+(((c0_4 y z w a b)*(c1_3 y z w a b))+(((c0_5 y z w a b)*(c1_2 y z w a b))+(((c0_6 y z w a b)*(c1_1 y z w a b))+(((c0_7 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*(((c2_5 y z w a b)*(c3_2 y z w a b))+(((c2_6 y z w a b)*(c3_1 y z w a b))+(((c2_7 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_5 y z w a b)*(c5_2 y z w a b))+(((c4_6 y z w a b)*(c5_1 y z w a b))+(((c4_7 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_5 y z w a b)*(c7_2 y z w a b))+(((c6_6 y z w a b)*(c7_1 y z w a b))+(((c6_7 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_4 y z w a b)*(c9_3 y z w a b))+(((c8_5 y z w a b)*(c9_2 y z w a b))+(((c8_6 y z w a b)*(c9_1 y z w a b))+(((c8_7 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_7 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c10_7,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_5,c2_6,c2_7,c3_0,c3_1,c3_2,c4_5,c4_6,c4_7,c5_0,c5_1,c5_2,c6_5,c6_6,c6_7,c7_0,c7_1,c7_2,c8_4,c8_5,c8_6,c8_7,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_7

theorem coefficient_8 (y z w a b : ℂ) : (certificate y z w a b)[8]?=some 0 := by
  change some (((((((((c0_2 y z w a b)*(c1_6 y z w a b))+(((c0_3 y z w a b)*(c1_5 y z w a b))+(((c0_4 y z w a b)*(c1_4 y z w a b))+(((c0_5 y z w a b)*(c1_3 y z w a b))+(((c0_6 y z w a b)*(c1_2 y z w a b))+(((c0_7 y z w a b)*(c1_1 y z w a b))+(((c0_8 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*(((c2_6 y z w a b)*(c3_2 y z w a b))+(((c2_7 y z w a b)*(c3_1 y z w a b))+(((c2_8 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_6 y z w a b)*(c5_2 y z w a b))+(((c4_7 y z w a b)*(c5_1 y z w a b))+(((c4_8 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_6 y z w a b)*(c7_2 y z w a b))+(((c6_7 y z w a b)*(c7_1 y z w a b))+(((c6_8 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_5 y z w a b)*(c9_3 y z w a b))+(((c8_6 y z w a b)*(c9_2 y z w a b))+(((c8_7 y z w a b)*(c9_1 y z w a b))+(((c8_8 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_8 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c10_8,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_6,c2_7,c2_8,c3_0,c3_1,c3_2,c4_6,c4_7,c4_8,c5_0,c5_1,c5_2,c6_6,c6_7,c6_8,c7_0,c7_1,c7_2,c8_5,c8_6,c8_7,c8_8,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_8
theorem coefficient_9 (y z w a b : ℂ) : (certificate y z w a b)[9]?=some 0 := by
  change some (((((((((c0_3 y z w a b)*(c1_6 y z w a b))+(((c0_4 y z w a b)*(c1_5 y z w a b))+(((c0_5 y z w a b)*(c1_4 y z w a b))+(((c0_6 y z w a b)*(c1_3 y z w a b))+(((c0_7 y z w a b)*(c1_2 y z w a b))+((c0_8 y z w a b)*(c1_1 y z w a b)))))))+((-1)*(((c2_7 y z w a b)*(c3_2 y z w a b))+(((c2_8 y z w a b)*(c3_1 y z w a b))+(((c2_9 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_7 y z w a b)*(c5_2 y z w a b))+(((c4_8 y z w a b)*(c5_1 y z w a b))+(((c4_9 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_7 y z w a b)*(c7_2 y z w a b))+(((c6_8 y z w a b)*(c7_1 y z w a b))+(((c6_9 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_6 y z w a b)*(c9_3 y z w a b))+(((c8_7 y z w a b)*(c9_2 y z w a b))+(((c8_8 y z w a b)*(c9_1 y z w a b))+(((c8_9 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_9 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c10_9,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_2,c4_7,c4_8,c4_9,c5_0,c5_1,c5_2,c6_7,c6_8,c6_9,c7_0,c7_1,c7_2,c8_6,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_9

theorem coefficient_10 (y z w a b : ℂ) : (certificate y z w a b)[10]?=some 0 := by
  change some (((((((((c0_4 y z w a b)*(c1_6 y z w a b))+(((c0_5 y z w a b)*(c1_5 y z w a b))+(((c0_6 y z w a b)*(c1_4 y z w a b))+(((c0_7 y z w a b)*(c1_3 y z w a b))+((c0_8 y z w a b)*(c1_2 y z w a b))))))+((-1)*(((c2_8 y z w a b)*(c3_2 y z w a b))+(((c2_9 y z w a b)*(c3_1 y z w a b))+(((c2_10 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_8 y z w a b)*(c5_2 y z w a b))+(((c4_9 y z w a b)*(c5_1 y z w a b))+(((c4_10 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_8 y z w a b)*(c7_2 y z w a b))+((c6_9 y z w a b)*(c7_1 y z w a b)))))+((-1)*(((c8_7 y z w a b)*(c9_3 y z w a b))+(((c8_8 y z w a b)*(c9_2 y z w a b))+(((c8_9 y z w a b)*(c9_1 y z w a b))+(((c8_10 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_10 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_4,c0_5,c0_6,c0_7,c0_8,c10_10,c1_2,c1_3,c1_4,c1_5,c1_6,c2_10,c2_8,c2_9,c3_0,c3_1,c3_2,c4_10,c4_8,c4_9,c5_0,c5_1,c5_2,c6_8,c6_9,c7_1,c7_2,c8_10,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_10
theorem coefficient_11 (y z w a b : ℂ) : (certificate y z w a b)[11]?=some 0 := by
  change some (((((((((c0_5 y z w a b)*(c1_6 y z w a b))+(((c0_6 y z w a b)*(c1_5 y z w a b))+(((c0_7 y z w a b)*(c1_4 y z w a b))+((c0_8 y z w a b)*(c1_3 y z w a b)))))+((-1)*(((c2_9 y z w a b)*(c3_2 y z w a b))+(((c2_10 y z w a b)*(c3_1 y z w a b))+(((c2_11 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_9 y z w a b)*(c5_2 y z w a b))+(((c4_10 y z w a b)*(c5_1 y z w a b))+(((c4_11 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*((c6_9 y z w a b)*(c7_2 y z w a b))))+((-1)*(((c8_8 y z w a b)*(c9_3 y z w a b))+(((c8_9 y z w a b)*(c9_2 y z w a b))+(((c8_10 y z w a b)*(c9_1 y z w a b))+(((c8_11 y z w a b)*(c9_0 y z w a b))+0))))))+((-1)*(c10_11 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_5,c0_6,c0_7,c0_8,c10_11,c1_3,c1_4,c1_5,c1_6,c2_10,c2_11,c2_9,c3_0,c3_1,c3_2,c4_10,c4_11,c4_9,c5_0,c5_1,c5_2,c6_9,c7_2,c8_10,c8_11,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_11

theorem coefficient_12 (y z w a b : ℂ) : (certificate y z w a b)[12]?=some 0 := by
  change some ((((((((c0_6 y z w a b)*(c1_6 y z w a b))+(((c0_7 y z w a b)*(c1_5 y z w a b))+((c0_8 y z w a b)*(c1_4 y z w a b))))+((-1)*(((c2_10 y z w a b)*(c3_2 y z w a b))+((c2_11 y z w a b)*(c3_1 y z w a b)))))+((-1)*(((c4_10 y z w a b)*(c5_2 y z w a b))+((c4_11 y z w a b)*(c5_1 y z w a b)))))+((-1)*(((c8_9 y z w a b)*(c9_3 y z w a b))+(((c8_10 y z w a b)*(c9_2 y z w a b))+((c8_11 y z w a b)*(c9_1 y z w a b))))))+((-1)*(c10_12 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_6,c0_7,c0_8,c10_12,c1_4,c1_5,c1_6,c2_10,c2_11,c3_1,c3_2,c4_10,c4_11,c5_1,c5_2,c8_10,c8_11,c8_9,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_12
theorem coefficient_13 (y z w a b : ℂ) : (certificate y z w a b)[13]?=some 0 := by
  change some ((((((((c0_7 y z w a b)*(c1_6 y z w a b))+((c0_8 y z w a b)*(c1_5 y z w a b)))+((-1)*((c2_11 y z w a b)*(c3_2 y z w a b))))+((-1)*((c4_11 y z w a b)*(c5_2 y z w a b))))+((-1)*(((c8_10 y z w a b)*(c9_3 y z w a b))+((c8_11 y z w a b)*(c9_2 y z w a b)))))+((-1)*(c10_13 y z w a b))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_7,c0_8,c10_13,c1_5,c1_6,c2_11,c3_2,c4_11,c5_2,c8_10,c8_11,c9_2,c9_3]
  ring
#print axioms coefficient_13

theorem coefficient_14 (y z w a b : ℂ) : (certificate y z w a b)[14]?=some 0 := by
  change some ((((c0_8 y z w a b)*(c1_6 y z w a b))+((-1)*((c8_11 y z w a b)*(c9_3 y z w a b)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_8,c1_6,c8_11,c9_3]
  ring
#print axioms coefficient_14

end SmallLevelTwentySixMMPPariSyzygy7Column1
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariSyzygy7Column2
open SmallLevelPolynomialCoefficientCertificate

theorem coefficient_0 (y z w a b : ℂ) : (certificate y z w a b)[0]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_0 y z w a b))+0)+((-1)*(((c2_0 y z w a b)*(c3_0 y z w a b))+0)))+((-1)*(((c4_0 y z w a b)*(c5_0 y z w a b))+0)))+((-1)*(((c6_0 y z w a b)*(c7_0 y z w a b))+0)))+((-1)*(((c8_0 y z w a b)*(c9_0 y z w a b))+0))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c1_0,c2_0,c3_0,c4_0,c5_0,c6_0,c7_0,c8_0,c9_0]
  ring
#print axioms coefficient_0
theorem coefficient_1 (y z w a b : ℂ) : (certificate y z w a b)[1]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_1 y z w a b))+(((c0_1 y z w a b)*(c1_0 y z w a b))+0))+((-1)*(((c2_0 y z w a b)*(c3_1 y z w a b))+(((c2_1 y z w a b)*(c3_0 y z w a b))+0))))+((-1)*(((c4_0 y z w a b)*(c5_1 y z w a b))+(((c4_1 y z w a b)*(c5_0 y z w a b))+0))))+((-1)*(((c6_0 y z w a b)*(c7_1 y z w a b))+(((c6_1 y z w a b)*(c7_0 y z w a b))+0))))+((-1)*(((c8_0 y z w a b)*(c9_1 y z w a b))+(((c8_1 y z w a b)*(c9_0 y z w a b))+0)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c1_0,c1_1,c2_0,c2_1,c3_0,c3_1,c4_0,c4_1,c5_0,c5_1,c6_0,c6_1,c7_0,c7_1,c8_0,c8_1,c9_0,c9_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (y z w a b : ℂ) : (certificate y z w a b)[2]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_2 y z w a b))+(((c0_1 y z w a b)*(c1_1 y z w a b))+(((c0_2 y z w a b)*(c1_0 y z w a b))+0)))+((-1)*(((c2_0 y z w a b)*(c3_2 y z w a b))+(((c2_1 y z w a b)*(c3_1 y z w a b))+(((c2_2 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_0 y z w a b)*(c5_2 y z w a b))+(((c4_1 y z w a b)*(c5_1 y z w a b))+(((c4_2 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_0 y z w a b)*(c7_2 y z w a b))+(((c6_1 y z w a b)*(c7_1 y z w a b))+(((c6_2 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_2 y z w a b))+(((c8_1 y z w a b)*(c9_1 y z w a b))+(((c8_2 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c1_0,c1_1,c1_2,c2_0,c2_1,c2_2,c3_0,c3_1,c3_2,c4_0,c4_1,c4_2,c5_0,c5_1,c5_2,c6_0,c6_1,c6_2,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_2
theorem coefficient_3 (y z w a b : ℂ) : (certificate y z w a b)[3]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_3 y z w a b))+(((c0_1 y z w a b)*(c1_2 y z w a b))+(((c0_2 y z w a b)*(c1_1 y z w a b))+(((c0_3 y z w a b)*(c1_0 y z w a b))+0))))+((-1)*(((c2_0 y z w a b)*(c3_3 y z w a b))+(((c2_1 y z w a b)*(c3_2 y z w a b))+(((c2_2 y z w a b)*(c3_1 y z w a b))+(((c2_3 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_0 y z w a b)*(c5_3 y z w a b))+(((c4_1 y z w a b)*(c5_2 y z w a b))+(((c4_2 y z w a b)*(c5_1 y z w a b))+(((c4_3 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_0 y z w a b)*(c7_3 y z w a b))+(((c6_1 y z w a b)*(c7_2 y z w a b))+(((c6_2 y z w a b)*(c7_1 y z w a b))+(((c6_3 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_0 y z w a b)*(c9_3 y z w a b))+(((c8_1 y z w a b)*(c9_2 y z w a b))+(((c8_2 y z w a b)*(c9_1 y z w a b))+(((c8_3 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c3_0,c3_1,c3_2,c3_3,c4_0,c4_1,c4_2,c4_3,c5_0,c5_1,c5_2,c5_3,c6_0,c6_1,c6_2,c6_3,c7_0,c7_1,c7_2,c7_3,c8_0,c8_1,c8_2,c8_3,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (y z w a b : ℂ) : (certificate y z w a b)[4]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_4 y z w a b))+(((c0_1 y z w a b)*(c1_3 y z w a b))+(((c0_2 y z w a b)*(c1_2 y z w a b))+(((c0_3 y z w a b)*(c1_1 y z w a b))+(((c0_4 y z w a b)*(c1_0 y z w a b))+0)))))+((-1)*(((c2_1 y z w a b)*(c3_3 y z w a b))+(((c2_2 y z w a b)*(c3_2 y z w a b))+(((c2_3 y z w a b)*(c3_1 y z w a b))+(((c2_4 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_1 y z w a b)*(c5_3 y z w a b))+(((c4_2 y z w a b)*(c5_2 y z w a b))+(((c4_3 y z w a b)*(c5_1 y z w a b))+(((c4_4 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_1 y z w a b)*(c7_3 y z w a b))+(((c6_2 y z w a b)*(c7_2 y z w a b))+(((c6_3 y z w a b)*(c7_1 y z w a b))+(((c6_4 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_0 y z w a b)*(c9_4 y z w a b))+(((c8_1 y z w a b)*(c9_3 y z w a b))+(((c8_2 y z w a b)*(c9_2 y z w a b))+(((c8_3 y z w a b)*(c9_1 y z w a b))+(((c8_4 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_0,c1_1,c1_2,c1_3,c1_4,c2_1,c2_2,c2_3,c2_4,c3_0,c3_1,c3_2,c3_3,c4_1,c4_2,c4_3,c4_4,c5_0,c5_1,c5_2,c5_3,c6_1,c6_2,c6_3,c6_4,c7_0,c7_1,c7_2,c7_3,c8_0,c8_1,c8_2,c8_3,c8_4,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_4
theorem coefficient_5 (y z w a b : ℂ) : (certificate y z w a b)[5]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_5 y z w a b))+(((c0_1 y z w a b)*(c1_4 y z w a b))+(((c0_2 y z w a b)*(c1_3 y z w a b))+(((c0_3 y z w a b)*(c1_2 y z w a b))+(((c0_4 y z w a b)*(c1_1 y z w a b))+(((c0_5 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*(((c2_2 y z w a b)*(c3_3 y z w a b))+(((c2_3 y z w a b)*(c3_2 y z w a b))+(((c2_4 y z w a b)*(c3_1 y z w a b))+(((c2_5 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_2 y z w a b)*(c5_3 y z w a b))+(((c4_3 y z w a b)*(c5_2 y z w a b))+(((c4_4 y z w a b)*(c5_1 y z w a b))+(((c4_5 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_2 y z w a b)*(c7_3 y z w a b))+(((c6_3 y z w a b)*(c7_2 y z w a b))+(((c6_4 y z w a b)*(c7_1 y z w a b))+(((c6_5 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_1 y z w a b)*(c9_4 y z w a b))+(((c8_2 y z w a b)*(c9_3 y z w a b))+(((c8_3 y z w a b)*(c9_2 y z w a b))+(((c8_4 y z w a b)*(c9_1 y z w a b))+(((c8_5 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_2,c2_3,c2_4,c2_5,c3_0,c3_1,c3_2,c3_3,c4_2,c4_3,c4_4,c4_5,c5_0,c5_1,c5_2,c5_3,c6_2,c6_3,c6_4,c6_5,c7_0,c7_1,c7_2,c7_3,c8_1,c8_2,c8_3,c8_4,c8_5,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_5

theorem coefficient_6 (y z w a b : ℂ) : (certificate y z w a b)[6]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_6 y z w a b))+(((c0_1 y z w a b)*(c1_5 y z w a b))+(((c0_2 y z w a b)*(c1_4 y z w a b))+(((c0_3 y z w a b)*(c1_3 y z w a b))+(((c0_4 y z w a b)*(c1_2 y z w a b))+(((c0_5 y z w a b)*(c1_1 y z w a b))+(((c0_6 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*(((c2_3 y z w a b)*(c3_3 y z w a b))+(((c2_4 y z w a b)*(c3_2 y z w a b))+(((c2_5 y z w a b)*(c3_1 y z w a b))+(((c2_6 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_3 y z w a b)*(c5_3 y z w a b))+(((c4_4 y z w a b)*(c5_2 y z w a b))+(((c4_5 y z w a b)*(c5_1 y z w a b))+(((c4_6 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_3 y z w a b)*(c7_3 y z w a b))+(((c6_4 y z w a b)*(c7_2 y z w a b))+(((c6_5 y z w a b)*(c7_1 y z w a b))+(((c6_6 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_2 y z w a b)*(c9_4 y z w a b))+(((c8_3 y z w a b)*(c9_3 y z w a b))+(((c8_4 y z w a b)*(c9_2 y z w a b))+(((c8_5 y z w a b)*(c9_1 y z w a b))+(((c8_6 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_3,c2_4,c2_5,c2_6,c3_0,c3_1,c3_2,c3_3,c4_3,c4_4,c4_5,c4_6,c5_0,c5_1,c5_2,c5_3,c6_3,c6_4,c6_5,c6_6,c7_0,c7_1,c7_2,c7_3,c8_2,c8_3,c8_4,c8_5,c8_6,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_6
theorem coefficient_7 (y z w a b : ℂ) : (certificate y z w a b)[7]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_7 y z w a b))+(((c0_1 y z w a b)*(c1_6 y z w a b))+(((c0_2 y z w a b)*(c1_5 y z w a b))+(((c0_3 y z w a b)*(c1_4 y z w a b))+(((c0_4 y z w a b)*(c1_3 y z w a b))+(((c0_5 y z w a b)*(c1_2 y z w a b))+(((c0_6 y z w a b)*(c1_1 y z w a b))+(((c0_7 y z w a b)*(c1_0 y z w a b))+0))))))))+((-1)*(((c2_4 y z w a b)*(c3_3 y z w a b))+(((c2_5 y z w a b)*(c3_2 y z w a b))+(((c2_6 y z w a b)*(c3_1 y z w a b))+(((c2_7 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_4 y z w a b)*(c5_3 y z w a b))+(((c4_5 y z w a b)*(c5_2 y z w a b))+(((c4_6 y z w a b)*(c5_1 y z w a b))+(((c4_7 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_4 y z w a b)*(c7_3 y z w a b))+(((c6_5 y z w a b)*(c7_2 y z w a b))+(((c6_6 y z w a b)*(c7_1 y z w a b))+(((c6_7 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_3 y z w a b)*(c9_4 y z w a b))+(((c8_4 y z w a b)*(c9_3 y z w a b))+(((c8_5 y z w a b)*(c9_2 y z w a b))+(((c8_6 y z w a b)*(c9_1 y z w a b))+(((c8_7 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c2_4,c2_5,c2_6,c2_7,c3_0,c3_1,c3_2,c3_3,c4_4,c4_5,c4_6,c4_7,c5_0,c5_1,c5_2,c5_3,c6_4,c6_5,c6_6,c6_7,c7_0,c7_1,c7_2,c7_3,c8_3,c8_4,c8_5,c8_6,c8_7,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_7

theorem coefficient_8 (y z w a b : ℂ) : (certificate y z w a b)[8]?=some 0 := by
  change some ((((((((c0_1 y z w a b)*(c1_7 y z w a b))+(((c0_2 y z w a b)*(c1_6 y z w a b))+(((c0_3 y z w a b)*(c1_5 y z w a b))+(((c0_4 y z w a b)*(c1_4 y z w a b))+(((c0_5 y z w a b)*(c1_3 y z w a b))+(((c0_6 y z w a b)*(c1_2 y z w a b))+(((c0_7 y z w a b)*(c1_1 y z w a b))+(((c0_8 y z w a b)*(c1_0 y z w a b))+0))))))))+((-1)*(((c2_5 y z w a b)*(c3_3 y z w a b))+(((c2_6 y z w a b)*(c3_2 y z w a b))+(((c2_7 y z w a b)*(c3_1 y z w a b))+(((c2_8 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_5 y z w a b)*(c5_3 y z w a b))+(((c4_6 y z w a b)*(c5_2 y z w a b))+(((c4_7 y z w a b)*(c5_1 y z w a b))+(((c4_8 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_5 y z w a b)*(c7_3 y z w a b))+(((c6_6 y z w a b)*(c7_2 y z w a b))+(((c6_7 y z w a b)*(c7_1 y z w a b))+(((c6_8 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_4 y z w a b)*(c9_4 y z w a b))+(((c8_5 y z w a b)*(c9_3 y z w a b))+(((c8_6 y z w a b)*(c9_2 y z w a b))+(((c8_7 y z w a b)*(c9_1 y z w a b))+(((c8_8 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c2_5,c2_6,c2_7,c2_8,c3_0,c3_1,c3_2,c3_3,c4_5,c4_6,c4_7,c4_8,c5_0,c5_1,c5_2,c5_3,c6_5,c6_6,c6_7,c6_8,c7_0,c7_1,c7_2,c7_3,c8_4,c8_5,c8_6,c8_7,c8_8,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_8
theorem coefficient_9 (y z w a b : ℂ) : (certificate y z w a b)[9]?=some 0 := by
  change some ((((((((c0_2 y z w a b)*(c1_7 y z w a b))+(((c0_3 y z w a b)*(c1_6 y z w a b))+(((c0_4 y z w a b)*(c1_5 y z w a b))+(((c0_5 y z w a b)*(c1_4 y z w a b))+(((c0_6 y z w a b)*(c1_3 y z w a b))+(((c0_7 y z w a b)*(c1_2 y z w a b))+((c0_8 y z w a b)*(c1_1 y z w a b))))))))+((-1)*(((c2_6 y z w a b)*(c3_3 y z w a b))+(((c2_7 y z w a b)*(c3_2 y z w a b))+(((c2_8 y z w a b)*(c3_1 y z w a b))+(((c2_9 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_6 y z w a b)*(c5_3 y z w a b))+(((c4_7 y z w a b)*(c5_2 y z w a b))+(((c4_8 y z w a b)*(c5_1 y z w a b))+(((c4_9 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_6 y z w a b)*(c7_3 y z w a b))+(((c6_7 y z w a b)*(c7_2 y z w a b))+(((c6_8 y z w a b)*(c7_1 y z w a b))+(((c6_9 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_5 y z w a b)*(c9_4 y z w a b))+(((c8_6 y z w a b)*(c9_3 y z w a b))+(((c8_7 y z w a b)*(c9_2 y z w a b))+(((c8_8 y z w a b)*(c9_1 y z w a b))+(((c8_9 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c2_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_2,c3_3,c4_6,c4_7,c4_8,c4_9,c5_0,c5_1,c5_2,c5_3,c6_6,c6_7,c6_8,c6_9,c7_0,c7_1,c7_2,c7_3,c8_5,c8_6,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_9

theorem coefficient_10 (y z w a b : ℂ) : (certificate y z w a b)[10]?=some 0 := by
  change some ((((((((c0_3 y z w a b)*(c1_7 y z w a b))+(((c0_4 y z w a b)*(c1_6 y z w a b))+(((c0_5 y z w a b)*(c1_5 y z w a b))+(((c0_6 y z w a b)*(c1_4 y z w a b))+(((c0_7 y z w a b)*(c1_3 y z w a b))+((c0_8 y z w a b)*(c1_2 y z w a b)))))))+((-1)*(((c2_7 y z w a b)*(c3_3 y z w a b))+(((c2_8 y z w a b)*(c3_2 y z w a b))+(((c2_9 y z w a b)*(c3_1 y z w a b))+(((c2_10 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_7 y z w a b)*(c5_3 y z w a b))+(((c4_8 y z w a b)*(c5_2 y z w a b))+(((c4_9 y z w a b)*(c5_1 y z w a b))+(((c4_10 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_7 y z w a b)*(c7_3 y z w a b))+(((c6_8 y z w a b)*(c7_2 y z w a b))+((c6_9 y z w a b)*(c7_1 y z w a b))))))+((-1)*(((c8_6 y z w a b)*(c9_4 y z w a b))+(((c8_7 y z w a b)*(c9_3 y z w a b))+(((c8_8 y z w a b)*(c9_2 y z w a b))+(((c8_9 y z w a b)*(c9_1 y z w a b))+(((c8_10 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c1_2,c1_3,c1_4,c1_5,c1_6,c1_7,c2_10,c2_7,c2_8,c2_9,c3_0,c3_1,c3_2,c3_3,c4_10,c4_7,c4_8,c4_9,c5_0,c5_1,c5_2,c5_3,c6_7,c6_8,c6_9,c7_1,c7_2,c7_3,c8_10,c8_6,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_10
theorem coefficient_11 (y z w a b : ℂ) : (certificate y z w a b)[11]?=some 0 := by
  change some ((((((((c0_4 y z w a b)*(c1_7 y z w a b))+(((c0_5 y z w a b)*(c1_6 y z w a b))+(((c0_6 y z w a b)*(c1_5 y z w a b))+(((c0_7 y z w a b)*(c1_4 y z w a b))+((c0_8 y z w a b)*(c1_3 y z w a b))))))+((-1)*(((c2_8 y z w a b)*(c3_3 y z w a b))+(((c2_9 y z w a b)*(c3_2 y z w a b))+(((c2_10 y z w a b)*(c3_1 y z w a b))+(((c2_11 y z w a b)*(c3_0 y z w a b))+0))))))+((-1)*(((c4_8 y z w a b)*(c5_3 y z w a b))+(((c4_9 y z w a b)*(c5_2 y z w a b))+(((c4_10 y z w a b)*(c5_1 y z w a b))+(((c4_11 y z w a b)*(c5_0 y z w a b))+0))))))+((-1)*(((c6_8 y z w a b)*(c7_3 y z w a b))+((c6_9 y z w a b)*(c7_2 y z w a b)))))+((-1)*(((c8_7 y z w a b)*(c9_4 y z w a b))+(((c8_8 y z w a b)*(c9_3 y z w a b))+(((c8_9 y z w a b)*(c9_2 y z w a b))+(((c8_10 y z w a b)*(c9_1 y z w a b))+(((c8_11 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_4,c0_5,c0_6,c0_7,c0_8,c1_3,c1_4,c1_5,c1_6,c1_7,c2_10,c2_11,c2_8,c2_9,c3_0,c3_1,c3_2,c3_3,c4_10,c4_11,c4_8,c4_9,c5_0,c5_1,c5_2,c5_3,c6_8,c6_9,c7_2,c7_3,c8_10,c8_11,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_11

theorem coefficient_12 (y z w a b : ℂ) : (certificate y z w a b)[12]?=some 0 := by
  change some ((((((((c0_5 y z w a b)*(c1_7 y z w a b))+(((c0_6 y z w a b)*(c1_6 y z w a b))+(((c0_7 y z w a b)*(c1_5 y z w a b))+((c0_8 y z w a b)*(c1_4 y z w a b)))))+((-1)*(((c2_9 y z w a b)*(c3_3 y z w a b))+(((c2_10 y z w a b)*(c3_2 y z w a b))+((c2_11 y z w a b)*(c3_1 y z w a b))))))+((-1)*(((c4_9 y z w a b)*(c5_3 y z w a b))+(((c4_10 y z w a b)*(c5_2 y z w a b))+((c4_11 y z w a b)*(c5_1 y z w a b))))))+((-1)*((c6_9 y z w a b)*(c7_3 y z w a b))))+((-1)*(((c8_8 y z w a b)*(c9_4 y z w a b))+(((c8_9 y z w a b)*(c9_3 y z w a b))+(((c8_10 y z w a b)*(c9_2 y z w a b))+((c8_11 y z w a b)*(c9_1 y z w a b))))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_5,c0_6,c0_7,c0_8,c1_4,c1_5,c1_6,c1_7,c2_10,c2_11,c2_9,c3_1,c3_2,c3_3,c4_10,c4_11,c4_9,c5_1,c5_2,c5_3,c6_9,c7_3,c8_10,c8_11,c8_8,c8_9,c9_1,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_12
theorem coefficient_13 (y z w a b : ℂ) : (certificate y z w a b)[13]?=some 0 := by
  change some (((((((c0_6 y z w a b)*(c1_7 y z w a b))+(((c0_7 y z w a b)*(c1_6 y z w a b))+((c0_8 y z w a b)*(c1_5 y z w a b))))+((-1)*(((c2_10 y z w a b)*(c3_3 y z w a b))+((c2_11 y z w a b)*(c3_2 y z w a b)))))+((-1)*(((c4_10 y z w a b)*(c5_3 y z w a b))+((c4_11 y z w a b)*(c5_2 y z w a b)))))+((-1)*(((c8_9 y z w a b)*(c9_4 y z w a b))+(((c8_10 y z w a b)*(c9_3 y z w a b))+((c8_11 y z w a b)*(c9_2 y z w a b)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_6,c0_7,c0_8,c1_5,c1_6,c1_7,c2_10,c2_11,c3_2,c3_3,c4_10,c4_11,c5_2,c5_3,c8_10,c8_11,c8_9,c9_2,c9_3,c9_4]
  ring
#print axioms coefficient_13

theorem coefficient_14 (y z w a b : ℂ) : (certificate y z w a b)[14]?=some 0 := by
  change some (((((((c0_7 y z w a b)*(c1_7 y z w a b))+((c0_8 y z w a b)*(c1_6 y z w a b)))+((-1)*((c2_11 y z w a b)*(c3_3 y z w a b))))+((-1)*((c4_11 y z w a b)*(c5_3 y z w a b))))+((-1)*(((c8_10 y z w a b)*(c9_4 y z w a b))+((c8_11 y z w a b)*(c9_3 y z w a b))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_7,c0_8,c1_6,c1_7,c2_11,c3_3,c4_11,c5_3,c8_10,c8_11,c9_3,c9_4]
  ring
#print axioms coefficient_14
theorem coefficient_15 (y z w a b : ℂ) : (certificate y z w a b)[15]?=some 0 := by
  change some ((((c0_8 y z w a b)*(c1_7 y z w a b))+((-1)*((c8_11 y z w a b)*(c9_4 y z w a b)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_8,c1_7,c8_11,c9_4]
  ring
#print axioms coefficient_15

end SmallLevelTwentySixMMPPariSyzygy7Column2
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariSyzygy7Column3
open SmallLevelPolynomialCoefficientCertificate

theorem coefficient_0 (y z w a b : ℂ) : (certificate y z w a b)[0]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_0 y z w a b))+0)+((-1)*(((c2_0 y z w a b)*(c3_0 y z w a b))+0)))+((-1)*(((c4_0 y z w a b)*(c5_0 y z w a b))+0)))+((-1)*(((c6_0 y z w a b)*(c7_0 y z w a b))+0)))+((-1)*(((c8_0 y z w a b)*(c9_0 y z w a b))+0))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c1_0,c2_0,c3_0,c4_0,c5_0,c6_0,c7_0,c8_0,c9_0]
  ring
#print axioms coefficient_0
theorem coefficient_1 (y z w a b : ℂ) : (certificate y z w a b)[1]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_1 y z w a b))+(((c0_1 y z w a b)*(c1_0 y z w a b))+0))+((-1)*(((c2_0 y z w a b)*(c3_1 y z w a b))+(((c2_1 y z w a b)*(c3_0 y z w a b))+0))))+((-1)*(((c4_0 y z w a b)*(c5_1 y z w a b))+(((c4_1 y z w a b)*(c5_0 y z w a b))+0))))+((-1)*(((c6_0 y z w a b)*(c7_1 y z w a b))+(((c6_1 y z w a b)*(c7_0 y z w a b))+0))))+((-1)*(((c8_0 y z w a b)*(c9_1 y z w a b))+(((c8_1 y z w a b)*(c9_0 y z w a b))+0)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c1_0,c1_1,c2_0,c2_1,c3_0,c3_1,c4_0,c4_1,c5_0,c5_1,c6_0,c6_1,c7_0,c7_1,c8_0,c8_1,c9_0,c9_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (y z w a b : ℂ) : (certificate y z w a b)[2]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_2 y z w a b))+(((c0_1 y z w a b)*(c1_1 y z w a b))+(((c0_2 y z w a b)*(c1_0 y z w a b))+0)))+((-1)*(((c2_0 y z w a b)*(c3_2 y z w a b))+(((c2_1 y z w a b)*(c3_1 y z w a b))+(((c2_2 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_0 y z w a b)*(c5_2 y z w a b))+(((c4_1 y z w a b)*(c5_1 y z w a b))+(((c4_2 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_0 y z w a b)*(c7_2 y z w a b))+(((c6_1 y z w a b)*(c7_1 y z w a b))+(((c6_2 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_2 y z w a b))+(((c8_1 y z w a b)*(c9_1 y z w a b))+(((c8_2 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c1_0,c1_1,c1_2,c2_0,c2_1,c2_2,c3_0,c3_1,c3_2,c4_0,c4_1,c4_2,c5_0,c5_1,c5_2,c6_0,c6_1,c6_2,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_2
theorem coefficient_3 (y z w a b : ℂ) : (certificate y z w a b)[3]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_3 y z w a b))+(((c0_1 y z w a b)*(c1_2 y z w a b))+(((c0_2 y z w a b)*(c1_1 y z w a b))+(((c0_3 y z w a b)*(c1_0 y z w a b))+0))))+((-1)*(((c2_1 y z w a b)*(c3_2 y z w a b))+(((c2_2 y z w a b)*(c3_1 y z w a b))+(((c2_3 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_1 y z w a b)*(c5_2 y z w a b))+(((c4_2 y z w a b)*(c5_1 y z w a b))+(((c4_3 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_1 y z w a b)*(c7_2 y z w a b))+(((c6_2 y z w a b)*(c7_1 y z w a b))+(((c6_3 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_3 y z w a b))+(((c8_1 y z w a b)*(c9_2 y z w a b))+(((c8_2 y z w a b)*(c9_1 y z w a b))+(((c8_3 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c1_0,c1_1,c1_2,c1_3,c2_1,c2_2,c2_3,c3_0,c3_1,c3_2,c4_1,c4_2,c4_3,c5_0,c5_1,c5_2,c6_1,c6_2,c6_3,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c8_3,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (y z w a b : ℂ) : (certificate y z w a b)[4]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_4 y z w a b))+(((c0_1 y z w a b)*(c1_3 y z w a b))+(((c0_2 y z w a b)*(c1_2 y z w a b))+(((c0_3 y z w a b)*(c1_1 y z w a b))+(((c0_4 y z w a b)*(c1_0 y z w a b))+0)))))+((-1)*(((c2_2 y z w a b)*(c3_2 y z w a b))+(((c2_3 y z w a b)*(c3_1 y z w a b))+(((c2_4 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_2 y z w a b)*(c5_2 y z w a b))+(((c4_3 y z w a b)*(c5_1 y z w a b))+(((c4_4 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_2 y z w a b)*(c7_2 y z w a b))+(((c6_3 y z w a b)*(c7_1 y z w a b))+(((c6_4 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_1 y z w a b)*(c9_3 y z w a b))+(((c8_2 y z w a b)*(c9_2 y z w a b))+(((c8_3 y z w a b)*(c9_1 y z w a b))+(((c8_4 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_0,c1_1,c1_2,c1_3,c1_4,c2_2,c2_3,c2_4,c3_0,c3_1,c3_2,c4_2,c4_3,c4_4,c5_0,c5_1,c5_2,c6_2,c6_3,c6_4,c7_0,c7_1,c7_2,c8_1,c8_2,c8_3,c8_4,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_4
theorem coefficient_5 (y z w a b : ℂ) : (certificate y z w a b)[5]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_5 y z w a b))+(((c0_1 y z w a b)*(c1_4 y z w a b))+(((c0_2 y z w a b)*(c1_3 y z w a b))+(((c0_3 y z w a b)*(c1_2 y z w a b))+(((c0_4 y z w a b)*(c1_1 y z w a b))+(((c0_5 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*(((c2_3 y z w a b)*(c3_2 y z w a b))+(((c2_4 y z w a b)*(c3_1 y z w a b))+(((c2_5 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_3 y z w a b)*(c5_2 y z w a b))+(((c4_4 y z w a b)*(c5_1 y z w a b))+(((c4_5 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_3 y z w a b)*(c7_2 y z w a b))+(((c6_4 y z w a b)*(c7_1 y z w a b))+(((c6_5 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_2 y z w a b)*(c9_3 y z w a b))+(((c8_3 y z w a b)*(c9_2 y z w a b))+(((c8_4 y z w a b)*(c9_1 y z w a b))+(((c8_5 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c2_3,c2_4,c2_5,c3_0,c3_1,c3_2,c4_3,c4_4,c4_5,c5_0,c5_1,c5_2,c6_3,c6_4,c6_5,c7_0,c7_1,c7_2,c8_2,c8_3,c8_4,c8_5,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_5

theorem coefficient_6 (y z w a b : ℂ) : (certificate y z w a b)[6]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_6 y z w a b))+(((c0_1 y z w a b)*(c1_5 y z w a b))+(((c0_2 y z w a b)*(c1_4 y z w a b))+(((c0_3 y z w a b)*(c1_3 y z w a b))+(((c0_4 y z w a b)*(c1_2 y z w a b))+(((c0_5 y z w a b)*(c1_1 y z w a b))+(((c0_6 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*(((c2_4 y z w a b)*(c3_2 y z w a b))+(((c2_5 y z w a b)*(c3_1 y z w a b))+(((c2_6 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_4 y z w a b)*(c5_2 y z w a b))+(((c4_5 y z w a b)*(c5_1 y z w a b))+(((c4_6 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_4 y z w a b)*(c7_2 y z w a b))+(((c6_5 y z w a b)*(c7_1 y z w a b))+(((c6_6 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_3 y z w a b)*(c9_3 y z w a b))+(((c8_4 y z w a b)*(c9_2 y z w a b))+(((c8_5 y z w a b)*(c9_1 y z w a b))+(((c8_6 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_4,c2_5,c2_6,c3_0,c3_1,c3_2,c4_4,c4_5,c4_6,c5_0,c5_1,c5_2,c6_4,c6_5,c6_6,c7_0,c7_1,c7_2,c8_3,c8_4,c8_5,c8_6,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_6
theorem coefficient_7 (y z w a b : ℂ) : (certificate y z w a b)[7]?=some 0 := by
  change some ((((((((c0_1 y z w a b)*(c1_6 y z w a b))+(((c0_2 y z w a b)*(c1_5 y z w a b))+(((c0_3 y z w a b)*(c1_4 y z w a b))+(((c0_4 y z w a b)*(c1_3 y z w a b))+(((c0_5 y z w a b)*(c1_2 y z w a b))+(((c0_6 y z w a b)*(c1_1 y z w a b))+(((c0_7 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*(((c2_5 y z w a b)*(c3_2 y z w a b))+(((c2_6 y z w a b)*(c3_1 y z w a b))+(((c2_7 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_5 y z w a b)*(c5_2 y z w a b))+(((c4_6 y z w a b)*(c5_1 y z w a b))+(((c4_7 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_5 y z w a b)*(c7_2 y z w a b))+(((c6_6 y z w a b)*(c7_1 y z w a b))+(((c6_7 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_4 y z w a b)*(c9_3 y z w a b))+(((c8_5 y z w a b)*(c9_2 y z w a b))+(((c8_6 y z w a b)*(c9_1 y z w a b))+(((c8_7 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_5,c2_6,c2_7,c3_0,c3_1,c3_2,c4_5,c4_6,c4_7,c5_0,c5_1,c5_2,c6_5,c6_6,c6_7,c7_0,c7_1,c7_2,c8_4,c8_5,c8_6,c8_7,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_7

theorem coefficient_8 (y z w a b : ℂ) : (certificate y z w a b)[8]?=some 0 := by
  change some ((((((((c0_2 y z w a b)*(c1_6 y z w a b))+(((c0_3 y z w a b)*(c1_5 y z w a b))+(((c0_4 y z w a b)*(c1_4 y z w a b))+(((c0_5 y z w a b)*(c1_3 y z w a b))+(((c0_6 y z w a b)*(c1_2 y z w a b))+(((c0_7 y z w a b)*(c1_1 y z w a b))+(((c0_8 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*(((c2_6 y z w a b)*(c3_2 y z w a b))+(((c2_7 y z w a b)*(c3_1 y z w a b))+(((c2_8 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_6 y z w a b)*(c5_2 y z w a b))+(((c4_7 y z w a b)*(c5_1 y z w a b))+(((c4_8 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_6 y z w a b)*(c7_2 y z w a b))+(((c6_7 y z w a b)*(c7_1 y z w a b))+(((c6_8 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_5 y z w a b)*(c9_3 y z w a b))+(((c8_6 y z w a b)*(c9_2 y z w a b))+(((c8_7 y z w a b)*(c9_1 y z w a b))+(((c8_8 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_6,c2_7,c2_8,c3_0,c3_1,c3_2,c4_6,c4_7,c4_8,c5_0,c5_1,c5_2,c6_6,c6_7,c6_8,c7_0,c7_1,c7_2,c8_5,c8_6,c8_7,c8_8,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_8
theorem coefficient_9 (y z w a b : ℂ) : (certificate y z w a b)[9]?=some 0 := by
  change some ((((((((c0_3 y z w a b)*(c1_6 y z w a b))+(((c0_4 y z w a b)*(c1_5 y z w a b))+(((c0_5 y z w a b)*(c1_4 y z w a b))+(((c0_6 y z w a b)*(c1_3 y z w a b))+(((c0_7 y z w a b)*(c1_2 y z w a b))+((c0_8 y z w a b)*(c1_1 y z w a b)))))))+((-1)*(((c2_7 y z w a b)*(c3_2 y z w a b))+(((c2_8 y z w a b)*(c3_1 y z w a b))+(((c2_9 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_7 y z w a b)*(c5_2 y z w a b))+(((c4_8 y z w a b)*(c5_1 y z w a b))+(((c4_9 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_7 y z w a b)*(c7_2 y z w a b))+(((c6_8 y z w a b)*(c7_1 y z w a b))+(((c6_9 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_6 y z w a b)*(c9_3 y z w a b))+(((c8_7 y z w a b)*(c9_2 y z w a b))+(((c8_8 y z w a b)*(c9_1 y z w a b))+(((c8_9 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c2_7,c2_8,c2_9,c3_0,c3_1,c3_2,c4_7,c4_8,c4_9,c5_0,c5_1,c5_2,c6_7,c6_8,c6_9,c7_0,c7_1,c7_2,c8_6,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_9

theorem coefficient_10 (y z w a b : ℂ) : (certificate y z w a b)[10]?=some 0 := by
  change some ((((((((c0_4 y z w a b)*(c1_6 y z w a b))+(((c0_5 y z w a b)*(c1_5 y z w a b))+(((c0_6 y z w a b)*(c1_4 y z w a b))+(((c0_7 y z w a b)*(c1_3 y z w a b))+((c0_8 y z w a b)*(c1_2 y z w a b))))))+((-1)*(((c2_8 y z w a b)*(c3_2 y z w a b))+(((c2_9 y z w a b)*(c3_1 y z w a b))+(((c2_10 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_8 y z w a b)*(c5_2 y z w a b))+(((c4_9 y z w a b)*(c5_1 y z w a b))+(((c4_10 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*(((c6_8 y z w a b)*(c7_2 y z w a b))+((c6_9 y z w a b)*(c7_1 y z w a b)))))+((-1)*(((c8_7 y z w a b)*(c9_3 y z w a b))+(((c8_8 y z w a b)*(c9_2 y z w a b))+(((c8_9 y z w a b)*(c9_1 y z w a b))+(((c8_10 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_4,c0_5,c0_6,c0_7,c0_8,c1_2,c1_3,c1_4,c1_5,c1_6,c2_10,c2_8,c2_9,c3_0,c3_1,c3_2,c4_10,c4_8,c4_9,c5_0,c5_1,c5_2,c6_8,c6_9,c7_1,c7_2,c8_10,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_10
theorem coefficient_11 (y z w a b : ℂ) : (certificate y z w a b)[11]?=some 0 := by
  change some ((((((((c0_5 y z w a b)*(c1_6 y z w a b))+(((c0_6 y z w a b)*(c1_5 y z w a b))+(((c0_7 y z w a b)*(c1_4 y z w a b))+((c0_8 y z w a b)*(c1_3 y z w a b)))))+((-1)*(((c2_9 y z w a b)*(c3_2 y z w a b))+(((c2_10 y z w a b)*(c3_1 y z w a b))+(((c2_11 y z w a b)*(c3_0 y z w a b))+0)))))+((-1)*(((c4_9 y z w a b)*(c5_2 y z w a b))+(((c4_10 y z w a b)*(c5_1 y z w a b))+(((c4_11 y z w a b)*(c5_0 y z w a b))+0)))))+((-1)*((c6_9 y z w a b)*(c7_2 y z w a b))))+((-1)*(((c8_8 y z w a b)*(c9_3 y z w a b))+(((c8_9 y z w a b)*(c9_2 y z w a b))+(((c8_10 y z w a b)*(c9_1 y z w a b))+(((c8_11 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_5,c0_6,c0_7,c0_8,c1_3,c1_4,c1_5,c1_6,c2_10,c2_11,c2_9,c3_0,c3_1,c3_2,c4_10,c4_11,c4_9,c5_0,c5_1,c5_2,c6_9,c7_2,c8_10,c8_11,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_11

theorem coefficient_12 (y z w a b : ℂ) : (certificate y z w a b)[12]?=some 0 := by
  change some (((((((c0_6 y z w a b)*(c1_6 y z w a b))+(((c0_7 y z w a b)*(c1_5 y z w a b))+((c0_8 y z w a b)*(c1_4 y z w a b))))+((-1)*(((c2_10 y z w a b)*(c3_2 y z w a b))+((c2_11 y z w a b)*(c3_1 y z w a b)))))+((-1)*(((c4_10 y z w a b)*(c5_2 y z w a b))+((c4_11 y z w a b)*(c5_1 y z w a b)))))+((-1)*(((c8_9 y z w a b)*(c9_3 y z w a b))+(((c8_10 y z w a b)*(c9_2 y z w a b))+((c8_11 y z w a b)*(c9_1 y z w a b)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_6,c0_7,c0_8,c1_4,c1_5,c1_6,c2_10,c2_11,c3_1,c3_2,c4_10,c4_11,c5_1,c5_2,c8_10,c8_11,c8_9,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_12
theorem coefficient_13 (y z w a b : ℂ) : (certificate y z w a b)[13]?=some 0 := by
  change some (((((((c0_7 y z w a b)*(c1_6 y z w a b))+((c0_8 y z w a b)*(c1_5 y z w a b)))+((-1)*((c2_11 y z w a b)*(c3_2 y z w a b))))+((-1)*((c4_11 y z w a b)*(c5_2 y z w a b))))+((-1)*(((c8_10 y z w a b)*(c9_3 y z w a b))+((c8_11 y z w a b)*(c9_2 y z w a b))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_7,c0_8,c1_5,c1_6,c2_11,c3_2,c4_11,c5_2,c8_10,c8_11,c9_2,c9_3]
  ring
#print axioms coefficient_13

theorem coefficient_14 (y z w a b : ℂ) : (certificate y z w a b)[14]?=some 0 := by
  change some ((((c0_8 y z w a b)*(c1_6 y z w a b))+((-1)*((c8_11 y z w a b)*(c9_3 y z w a b)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_8,c1_6,c8_11,c9_3]
  ring
#print axioms coefficient_14

end SmallLevelTwentySixMMPPariSyzygy7Column3
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariSyzygy7Column4
open SmallLevelPolynomialCoefficientCertificate

theorem coefficient_0 (y z w a b : ℂ) : (certificate y z w a b)[0]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_0 y z w a b))+0)+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_0 y z w a b))+0)))+((-1)*(((c8_0 y z w a b)*(c9_0 y z w a b))+0))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c1_0,c6_0,c7_0,c8_0,c9_0]
  ring
#print axioms coefficient_0
theorem coefficient_1 (y z w a b : ℂ) : (certificate y z w a b)[1]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_1 y z w a b))+(((c0_1 y z w a b)*(c1_0 y z w a b))+0))+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_1 y z w a b))+(((c6_1 y z w a b)*(c7_0 y z w a b))+0))))+((-1)*(((c8_0 y z w a b)*(c9_1 y z w a b))+(((c8_1 y z w a b)*(c9_0 y z w a b))+0)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c1_0,c1_1,c6_0,c6_1,c7_0,c7_1,c8_0,c8_1,c9_0,c9_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (y z w a b : ℂ) : (certificate y z w a b)[2]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_2 y z w a b))+(((c0_1 y z w a b)*(c1_1 y z w a b))+(((c0_2 y z w a b)*(c1_0 y z w a b))+0)))+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_2 y z w a b))+(((c6_1 y z w a b)*(c7_1 y z w a b))+(((c6_2 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_2 y z w a b))+(((c8_1 y z w a b)*(c9_1 y z w a b))+(((c8_2 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c1_0,c1_1,c1_2,c6_0,c6_1,c6_2,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_2
theorem coefficient_3 (y z w a b : ℂ) : (certificate y z w a b)[3]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_3 y z w a b))+(((c0_1 y z w a b)*(c1_2 y z w a b))+(((c0_2 y z w a b)*(c1_1 y z w a b))+(((c0_3 y z w a b)*(c1_0 y z w a b))+0))))+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_3 y z w a b))+(((c6_1 y z w a b)*(c7_2 y z w a b))+(((c6_2 y z w a b)*(c7_1 y z w a b))+(((c6_3 y z w a b)*(c7_0 y z w a b))+0))))))+((-1)*(((c8_1 y z w a b)*(c9_2 y z w a b))+(((c8_2 y z w a b)*(c9_1 y z w a b))+(((c8_3 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c1_0,c1_1,c1_2,c1_3,c6_0,c6_1,c6_2,c6_3,c7_0,c7_1,c7_2,c7_3,c8_1,c8_2,c8_3,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_3

theorem coefficient_4 (y z w a b : ℂ) : (certificate y z w a b)[4]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_4 y z w a b))+(((c0_1 y z w a b)*(c1_3 y z w a b))+(((c0_2 y z w a b)*(c1_2 y z w a b))+(((c0_3 y z w a b)*(c1_1 y z w a b))+(((c0_4 y z w a b)*(c1_0 y z w a b))+0)))))+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_4 y z w a b))+(((c6_1 y z w a b)*(c7_3 y z w a b))+(((c6_2 y z w a b)*(c7_2 y z w a b))+(((c6_3 y z w a b)*(c7_1 y z w a b))+(((c6_4 y z w a b)*(c7_0 y z w a b))+0)))))))+((-1)*(((c8_2 y z w a b)*(c9_2 y z w a b))+(((c8_3 y z w a b)*(c9_1 y z w a b))+(((c8_4 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_0,c1_1,c1_2,c1_3,c1_4,c6_0,c6_1,c6_2,c6_3,c6_4,c7_0,c7_1,c7_2,c7_3,c7_4,c8_2,c8_3,c8_4,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_4
theorem coefficient_5 (y z w a b : ℂ) : (certificate y z w a b)[5]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_5 y z w a b))+(((c0_1 y z w a b)*(c1_4 y z w a b))+(((c0_2 y z w a b)*(c1_3 y z w a b))+(((c0_3 y z w a b)*(c1_2 y z w a b))+(((c0_4 y z w a b)*(c1_1 y z w a b))+(((c0_5 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_1 y z w a b)*(c7_4 y z w a b))+(((c6_2 y z w a b)*(c7_3 y z w a b))+(((c6_3 y z w a b)*(c7_2 y z w a b))+(((c6_4 y z w a b)*(c7_1 y z w a b))+(((c6_5 y z w a b)*(c7_0 y z w a b))+0)))))))+((-1)*(((c8_3 y z w a b)*(c9_2 y z w a b))+(((c8_4 y z w a b)*(c9_1 y z w a b))+(((c8_5 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c6_1,c6_2,c6_3,c6_4,c6_5,c7_0,c7_1,c7_2,c7_3,c7_4,c8_3,c8_4,c8_5,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_5

theorem coefficient_6 (y z w a b : ℂ) : (certificate y z w a b)[6]?=some 0 := by
  change some ((((((((c0_1 y z w a b)*(c1_5 y z w a b))+(((c0_2 y z w a b)*(c1_4 y z w a b))+(((c0_3 y z w a b)*(c1_3 y z w a b))+(((c0_4 y z w a b)*(c1_2 y z w a b))+(((c0_5 y z w a b)*(c1_1 y z w a b))+(((c0_6 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_2 y z w a b)*(c7_4 y z w a b))+(((c6_3 y z w a b)*(c7_3 y z w a b))+(((c6_4 y z w a b)*(c7_2 y z w a b))+(((c6_5 y z w a b)*(c7_1 y z w a b))+(((c6_6 y z w a b)*(c7_0 y z w a b))+0)))))))+((-1)*(((c8_4 y z w a b)*(c9_2 y z w a b))+(((c8_5 y z w a b)*(c9_1 y z w a b))+(((c8_6 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c6_2,c6_3,c6_4,c6_5,c6_6,c7_0,c7_1,c7_2,c7_3,c7_4,c8_4,c8_5,c8_6,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_6
theorem coefficient_7 (y z w a b : ℂ) : (certificate y z w a b)[7]?=some 0 := by
  change some ((((((((c0_2 y z w a b)*(c1_5 y z w a b))+(((c0_3 y z w a b)*(c1_4 y z w a b))+(((c0_4 y z w a b)*(c1_3 y z w a b))+(((c0_5 y z w a b)*(c1_2 y z w a b))+(((c0_6 y z w a b)*(c1_1 y z w a b))+(((c0_7 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_3 y z w a b)*(c7_4 y z w a b))+(((c6_4 y z w a b)*(c7_3 y z w a b))+(((c6_5 y z w a b)*(c7_2 y z w a b))+(((c6_6 y z w a b)*(c7_1 y z w a b))+(((c6_7 y z w a b)*(c7_0 y z w a b))+0)))))))+((-1)*(((c8_5 y z w a b)*(c9_2 y z w a b))+(((c8_6 y z w a b)*(c9_1 y z w a b))+(((c8_7 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c6_3,c6_4,c6_5,c6_6,c6_7,c7_0,c7_1,c7_2,c7_3,c7_4,c8_5,c8_6,c8_7,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_7

theorem coefficient_8 (y z w a b : ℂ) : (certificate y z w a b)[8]?=some 0 := by
  change some ((((((((c0_3 y z w a b)*(c1_5 y z w a b))+(((c0_4 y z w a b)*(c1_4 y z w a b))+(((c0_5 y z w a b)*(c1_3 y z w a b))+(((c0_6 y z w a b)*(c1_2 y z w a b))+(((c0_7 y z w a b)*(c1_1 y z w a b))+(((c0_8 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_4 y z w a b)*(c7_4 y z w a b))+(((c6_5 y z w a b)*(c7_3 y z w a b))+(((c6_6 y z w a b)*(c7_2 y z w a b))+(((c6_7 y z w a b)*(c7_1 y z w a b))+(((c6_8 y z w a b)*(c7_0 y z w a b))+0)))))))+((-1)*(((c8_6 y z w a b)*(c9_2 y z w a b))+(((c8_7 y z w a b)*(c9_1 y z w a b))+(((c8_8 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c6_4,c6_5,c6_6,c6_7,c6_8,c7_0,c7_1,c7_2,c7_3,c7_4,c8_6,c8_7,c8_8,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_8
theorem coefficient_9 (y z w a b : ℂ) : (certificate y z w a b)[9]?=some 0 := by
  change some ((((((((c0_4 y z w a b)*(c1_5 y z w a b))+(((c0_5 y z w a b)*(c1_4 y z w a b))+(((c0_6 y z w a b)*(c1_3 y z w a b))+(((c0_7 y z w a b)*(c1_2 y z w a b))+((c0_8 y z w a b)*(c1_1 y z w a b))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_5 y z w a b)*(c7_4 y z w a b))+(((c6_6 y z w a b)*(c7_3 y z w a b))+(((c6_7 y z w a b)*(c7_2 y z w a b))+(((c6_8 y z w a b)*(c7_1 y z w a b))+(((c6_9 y z w a b)*(c7_0 y z w a b))+0)))))))+((-1)*(((c8_7 y z w a b)*(c9_2 y z w a b))+(((c8_8 y z w a b)*(c9_1 y z w a b))+(((c8_9 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_4,c0_5,c0_6,c0_7,c0_8,c1_1,c1_2,c1_3,c1_4,c1_5,c6_5,c6_6,c6_7,c6_8,c6_9,c7_0,c7_1,c7_2,c7_3,c7_4,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_9

theorem coefficient_10 (y z w a b : ℂ) : (certificate y z w a b)[10]?=some 0 := by
  change some ((((((((c0_5 y z w a b)*(c1_5 y z w a b))+(((c0_6 y z w a b)*(c1_4 y z w a b))+(((c0_7 y z w a b)*(c1_3 y z w a b))+((c0_8 y z w a b)*(c1_2 y z w a b)))))+((-1)*0))+((-1)*0))+((-1)*(((c6_6 y z w a b)*(c7_4 y z w a b))+(((c6_7 y z w a b)*(c7_3 y z w a b))+(((c6_8 y z w a b)*(c7_2 y z w a b))+((c6_9 y z w a b)*(c7_1 y z w a b)))))))+((-1)*(((c8_8 y z w a b)*(c9_2 y z w a b))+(((c8_9 y z w a b)*(c9_1 y z w a b))+(((c8_10 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_5,c0_6,c0_7,c0_8,c1_2,c1_3,c1_4,c1_5,c6_6,c6_7,c6_8,c6_9,c7_1,c7_2,c7_3,c7_4,c8_10,c8_8,c8_9,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_10
theorem coefficient_11 (y z w a b : ℂ) : (certificate y z w a b)[11]?=some 0 := by
  change some ((((((((c0_6 y z w a b)*(c1_5 y z w a b))+(((c0_7 y z w a b)*(c1_4 y z w a b))+((c0_8 y z w a b)*(c1_3 y z w a b))))+((-1)*0))+((-1)*0))+((-1)*(((c6_7 y z w a b)*(c7_4 y z w a b))+(((c6_8 y z w a b)*(c7_3 y z w a b))+((c6_9 y z w a b)*(c7_2 y z w a b))))))+((-1)*(((c8_9 y z w a b)*(c9_2 y z w a b))+(((c8_10 y z w a b)*(c9_1 y z w a b))+(((c8_11 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_6,c0_7,c0_8,c1_3,c1_4,c1_5,c6_7,c6_8,c6_9,c7_2,c7_3,c7_4,c8_10,c8_11,c8_9,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_11

theorem coefficient_12 (y z w a b : ℂ) : (certificate y z w a b)[12]?=some 0 := by
  change some ((((((c0_7 y z w a b)*(c1_5 y z w a b))+((c0_8 y z w a b)*(c1_4 y z w a b)))+((-1)*(((c6_8 y z w a b)*(c7_4 y z w a b))+((c6_9 y z w a b)*(c7_3 y z w a b)))))+((-1)*(((c8_10 y z w a b)*(c9_2 y z w a b))+((c8_11 y z w a b)*(c9_1 y z w a b))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_7,c0_8,c1_4,c1_5,c6_8,c6_9,c7_3,c7_4,c8_10,c8_11,c9_1,c9_2]
  ring
#print axioms coefficient_12
theorem coefficient_13 (y z w a b : ℂ) : (certificate y z w a b)[13]?=some 0 := by
  change some (((((c0_8 y z w a b)*(c1_5 y z w a b))+((-1)*((c6_9 y z w a b)*(c7_4 y z w a b))))+((-1)*((c8_11 y z w a b)*(c9_2 y z w a b)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_8,c1_5,c6_9,c7_4,c8_11,c9_2]
  ring
#print axioms coefficient_13

end SmallLevelTwentySixMMPPariSyzygy7Column4
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariSyzygy7Column5
open SmallLevelPolynomialCoefficientCertificate

theorem coefficient_0 (y z w a b : ℂ) : (certificate y z w a b)[0]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_0 y z w a b))+0)+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_0 y z w a b))+0)))+((-1)*(((c8_0 y z w a b)*(c9_0 y z w a b))+0))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c1_0,c6_0,c7_0,c8_0,c9_0]
  ring
#print axioms coefficient_0
theorem coefficient_1 (y z w a b : ℂ) : (certificate y z w a b)[1]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_1 y z w a b))+(((c0_1 y z w a b)*(c1_0 y z w a b))+0))+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_1 y z w a b))+(((c6_1 y z w a b)*(c7_0 y z w a b))+0))))+((-1)*(((c8_0 y z w a b)*(c9_1 y z w a b))+(((c8_1 y z w a b)*(c9_0 y z w a b))+0)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c1_0,c1_1,c6_0,c6_1,c7_0,c7_1,c8_0,c8_1,c9_0,c9_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (y z w a b : ℂ) : (certificate y z w a b)[2]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_2 y z w a b))+(((c0_1 y z w a b)*(c1_1 y z w a b))+(((c0_2 y z w a b)*(c1_0 y z w a b))+0)))+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_2 y z w a b))+(((c6_1 y z w a b)*(c7_1 y z w a b))+(((c6_2 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_2 y z w a b))+(((c8_1 y z w a b)*(c9_1 y z w a b))+(((c8_2 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c1_0,c1_1,c1_2,c6_0,c6_1,c6_2,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c9_0,c9_1,c9_2]
  ring
#print axioms coefficient_2
theorem coefficient_3 (y z w a b : ℂ) : (certificate y z w a b)[3]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_3 y z w a b))+(((c0_1 y z w a b)*(c1_2 y z w a b))+(((c0_2 y z w a b)*(c1_1 y z w a b))+(((c0_3 y z w a b)*(c1_0 y z w a b))+0))))+((-1)*0))+((-1)*0))+((-1)*(((c6_1 y z w a b)*(c7_2 y z w a b))+(((c6_2 y z w a b)*(c7_1 y z w a b))+(((c6_3 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_3 y z w a b))+(((c8_1 y z w a b)*(c9_2 y z w a b))+(((c8_2 y z w a b)*(c9_1 y z w a b))+(((c8_3 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c1_0,c1_1,c1_2,c1_3,c6_1,c6_2,c6_3,c7_0,c7_1,c7_2,c8_0,c8_1,c8_2,c8_3,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (y z w a b : ℂ) : (certificate y z w a b)[4]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_4 y z w a b))+(((c0_1 y z w a b)*(c1_3 y z w a b))+(((c0_2 y z w a b)*(c1_2 y z w a b))+(((c0_3 y z w a b)*(c1_1 y z w a b))+(((c0_4 y z w a b)*(c1_0 y z w a b))+0)))))+((-1)*0))+((-1)*0))+((-1)*(((c6_2 y z w a b)*(c7_2 y z w a b))+(((c6_3 y z w a b)*(c7_1 y z w a b))+(((c6_4 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_1 y z w a b)*(c9_3 y z w a b))+(((c8_2 y z w a b)*(c9_2 y z w a b))+(((c8_3 y z w a b)*(c9_1 y z w a b))+(((c8_4 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_0,c1_1,c1_2,c1_3,c1_4,c6_2,c6_3,c6_4,c7_0,c7_1,c7_2,c8_1,c8_2,c8_3,c8_4,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_4
theorem coefficient_5 (y z w a b : ℂ) : (certificate y z w a b)[5]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_5 y z w a b))+(((c0_1 y z w a b)*(c1_4 y z w a b))+(((c0_2 y z w a b)*(c1_3 y z w a b))+(((c0_3 y z w a b)*(c1_2 y z w a b))+(((c0_4 y z w a b)*(c1_1 y z w a b))+(((c0_5 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_3 y z w a b)*(c7_2 y z w a b))+(((c6_4 y z w a b)*(c7_1 y z w a b))+(((c6_5 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_2 y z w a b)*(c9_3 y z w a b))+(((c8_3 y z w a b)*(c9_2 y z w a b))+(((c8_4 y z w a b)*(c9_1 y z w a b))+(((c8_5 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c6_3,c6_4,c6_5,c7_0,c7_1,c7_2,c8_2,c8_3,c8_4,c8_5,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_5

theorem coefficient_6 (y z w a b : ℂ) : (certificate y z w a b)[6]?=some 0 := by
  change some ((((((((c0_0 y z w a b)*(c1_6 y z w a b))+(((c0_1 y z w a b)*(c1_5 y z w a b))+(((c0_2 y z w a b)*(c1_4 y z w a b))+(((c0_3 y z w a b)*(c1_3 y z w a b))+(((c0_4 y z w a b)*(c1_2 y z w a b))+(((c0_5 y z w a b)*(c1_1 y z w a b))+(((c0_6 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_4 y z w a b)*(c7_2 y z w a b))+(((c6_5 y z w a b)*(c7_1 y z w a b))+(((c6_6 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_3 y z w a b)*(c9_3 y z w a b))+(((c8_4 y z w a b)*(c9_2 y z w a b))+(((c8_5 y z w a b)*(c9_1 y z w a b))+(((c8_6 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c6_4,c6_5,c6_6,c7_0,c7_1,c7_2,c8_3,c8_4,c8_5,c8_6,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_6
theorem coefficient_7 (y z w a b : ℂ) : (certificate y z w a b)[7]?=some 0 := by
  change some ((((((((c0_1 y z w a b)*(c1_6 y z w a b))+(((c0_2 y z w a b)*(c1_5 y z w a b))+(((c0_3 y z w a b)*(c1_4 y z w a b))+(((c0_4 y z w a b)*(c1_3 y z w a b))+(((c0_5 y z w a b)*(c1_2 y z w a b))+(((c0_6 y z w a b)*(c1_1 y z w a b))+(((c0_7 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_5 y z w a b)*(c7_2 y z w a b))+(((c6_6 y z w a b)*(c7_1 y z w a b))+(((c6_7 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_4 y z w a b)*(c9_3 y z w a b))+(((c8_5 y z w a b)*(c9_2 y z w a b))+(((c8_6 y z w a b)*(c9_1 y z w a b))+(((c8_7 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_1,c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c6_5,c6_6,c6_7,c7_0,c7_1,c7_2,c8_4,c8_5,c8_6,c8_7,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_7

theorem coefficient_8 (y z w a b : ℂ) : (certificate y z w a b)[8]?=some 0 := by
  change some ((((((((c0_2 y z w a b)*(c1_6 y z w a b))+(((c0_3 y z w a b)*(c1_5 y z w a b))+(((c0_4 y z w a b)*(c1_4 y z w a b))+(((c0_5 y z w a b)*(c1_3 y z w a b))+(((c0_6 y z w a b)*(c1_2 y z w a b))+(((c0_7 y z w a b)*(c1_1 y z w a b))+(((c0_8 y z w a b)*(c1_0 y z w a b))+0)))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_6 y z w a b)*(c7_2 y z w a b))+(((c6_7 y z w a b)*(c7_1 y z w a b))+(((c6_8 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_5 y z w a b)*(c9_3 y z w a b))+(((c8_6 y z w a b)*(c9_2 y z w a b))+(((c8_7 y z w a b)*(c9_1 y z w a b))+(((c8_8 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_2,c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c1_0,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c6_6,c6_7,c6_8,c7_0,c7_1,c7_2,c8_5,c8_6,c8_7,c8_8,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_8
theorem coefficient_9 (y z w a b : ℂ) : (certificate y z w a b)[9]?=some 0 := by
  change some ((((((((c0_3 y z w a b)*(c1_6 y z w a b))+(((c0_4 y z w a b)*(c1_5 y z w a b))+(((c0_5 y z w a b)*(c1_4 y z w a b))+(((c0_6 y z w a b)*(c1_3 y z w a b))+(((c0_7 y z w a b)*(c1_2 y z w a b))+((c0_8 y z w a b)*(c1_1 y z w a b)))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_7 y z w a b)*(c7_2 y z w a b))+(((c6_8 y z w a b)*(c7_1 y z w a b))+(((c6_9 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_6 y z w a b)*(c9_3 y z w a b))+(((c8_7 y z w a b)*(c9_2 y z w a b))+(((c8_8 y z w a b)*(c9_1 y z w a b))+(((c8_9 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_3,c0_4,c0_5,c0_6,c0_7,c0_8,c1_1,c1_2,c1_3,c1_4,c1_5,c1_6,c6_7,c6_8,c6_9,c7_0,c7_1,c7_2,c8_6,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_9

theorem coefficient_10 (y z w a b : ℂ) : (certificate y z w a b)[10]?=some 0 := by
  change some ((((((((c0_4 y z w a b)*(c1_6 y z w a b))+(((c0_5 y z w a b)*(c1_5 y z w a b))+(((c0_6 y z w a b)*(c1_4 y z w a b))+(((c0_7 y z w a b)*(c1_3 y z w a b))+((c0_8 y z w a b)*(c1_2 y z w a b))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_8 y z w a b)*(c7_2 y z w a b))+((c6_9 y z w a b)*(c7_1 y z w a b)))))+((-1)*(((c8_7 y z w a b)*(c9_3 y z w a b))+(((c8_8 y z w a b)*(c9_2 y z w a b))+(((c8_9 y z w a b)*(c9_1 y z w a b))+(((c8_10 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_4,c0_5,c0_6,c0_7,c0_8,c1_2,c1_3,c1_4,c1_5,c1_6,c6_8,c6_9,c7_1,c7_2,c8_10,c8_7,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_10
theorem coefficient_11 (y z w a b : ℂ) : (certificate y z w a b)[11]?=some 0 := by
  change some ((((((((c0_5 y z w a b)*(c1_6 y z w a b))+(((c0_6 y z w a b)*(c1_5 y z w a b))+(((c0_7 y z w a b)*(c1_4 y z w a b))+((c0_8 y z w a b)*(c1_3 y z w a b)))))+((-1)*0))+((-1)*0))+((-1)*((c6_9 y z w a b)*(c7_2 y z w a b))))+((-1)*(((c8_8 y z w a b)*(c9_3 y z w a b))+(((c8_9 y z w a b)*(c9_2 y z w a b))+(((c8_10 y z w a b)*(c9_1 y z w a b))+(((c8_11 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_5,c0_6,c0_7,c0_8,c1_3,c1_4,c1_5,c1_6,c6_9,c7_2,c8_10,c8_11,c8_8,c8_9,c9_0,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_11

theorem coefficient_12 (y z w a b : ℂ) : (certificate y z w a b)[12]?=some 0 := by
  change some (((((c0_6 y z w a b)*(c1_6 y z w a b))+(((c0_7 y z w a b)*(c1_5 y z w a b))+((c0_8 y z w a b)*(c1_4 y z w a b))))+((-1)*(((c8_9 y z w a b)*(c9_3 y z w a b))+(((c8_10 y z w a b)*(c9_2 y z w a b))+((c8_11 y z w a b)*(c9_1 y z w a b)))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_6,c0_7,c0_8,c1_4,c1_5,c1_6,c8_10,c8_11,c8_9,c9_1,c9_2,c9_3]
  ring
#print axioms coefficient_12
theorem coefficient_13 (y z w a b : ℂ) : (certificate y z w a b)[13]?=some 0 := by
  change some (((((c0_7 y z w a b)*(c1_6 y z w a b))+((c0_8 y z w a b)*(c1_5 y z w a b)))+((-1)*(((c8_10 y z w a b)*(c9_3 y z w a b))+((c8_11 y z w a b)*(c9_2 y z w a b))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_7,c0_8,c1_5,c1_6,c8_10,c8_11,c9_2,c9_3]
  ring
#print axioms coefficient_13

theorem coefficient_14 (y z w a b : ℂ) : (certificate y z w a b)[14]?=some 0 := by
  change some ((((c0_8 y z w a b)*(c1_6 y z w a b))+((-1)*((c8_11 y z w a b)*(c9_3 y z w a b)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_8,c1_6,c8_11,c9_3]
  ring
#print axioms coefficient_14

end SmallLevelTwentySixMMPPariSyzygy7Column5
end

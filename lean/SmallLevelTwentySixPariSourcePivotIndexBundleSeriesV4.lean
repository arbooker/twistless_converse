module
public import SmallLevelTwentySixPariSourcePivotIndexDataSeriesV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixPariSourcePivot87
open SmallLevelPolynomialCoefficientCertificate

theorem coefficient_0 (y z w a b u : ℂ) :
    (certificate y z w a b u)[0]?=some 0 := by
  change some (((((c0_0 y z w a b u)*(c1_0 y z w a b u))+0)+(((c2_0 y z w a b u)*(c3_0 y z w a b u))+0))+(((-1)*(c4_0 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_0 y z w a b u))+0))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c1_0,c2_0,c3_0,c4_0,c5_0,c6_0]
  ring
#print axioms coefficient_0
theorem coefficient_1 (y z w a b u : ℂ) :
    (certificate y z w a b u)[1]?=some 0 := by
  change some (((((c0_0 y z w a b u)*(c1_1 y z w a b u))+(((c0_1 y z w a b u)*(c1_0 y z w a b u))+0))+(((c2_0 y z w a b u)*(c3_1 y z w a b u))+(((c2_1 y z w a b u)*(c3_0 y z w a b u))+0)))+(((-1)*(c4_1 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_1 y z w a b u))+(((c5_1 y z w a b u)*(c6_0 y z w a b u))+0)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c1_0,c1_1,c2_0,c2_1,c3_0,c3_1,c4_1,c5_0,c5_1,c6_0,c6_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (y z w a b u : ℂ) :
    (certificate y z w a b u)[2]?=some 0 := by
  change some (((((c0_0 y z w a b u)*(c1_2 y z w a b u))+(((c0_1 y z w a b u)*(c1_1 y z w a b u))+(((c0_2 y z w a b u)*(c1_0 y z w a b u))+0)))+(((c2_0 y z w a b u)*(c3_2 y z w a b u))+(((c2_1 y z w a b u)*(c3_1 y z w a b u))+(((c2_2 y z w a b u)*(c3_0 y z w a b u))+0))))+(((-1)*(c4_2 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_2 y z w a b u))+((c5_1 y z w a b u)*(c6_1 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c1_0,c1_1,c1_2,c2_0,c2_1,c2_2,c3_0,c3_1,c3_2,c4_2,c5_0,c5_1,c6_1,c6_2]
  ring
#print axioms coefficient_2
theorem coefficient_3 (y z w a b u : ℂ) :
    (certificate y z w a b u)[3]?=some 0 := by
  change some (((((c0_0 y z w a b u)*(c1_3 y z w a b u))+(((c0_1 y z w a b u)*(c1_2 y z w a b u))+(((c0_2 y z w a b u)*(c1_1 y z w a b u))+(((c0_3 y z w a b u)*(c1_0 y z w a b u))+0))))+(((c2_0 y z w a b u)*(c3_3 y z w a b u))+(((c2_1 y z w a b u)*(c3_2 y z w a b u))+(((c2_2 y z w a b u)*(c3_1 y z w a b u))+(((c2_3 y z w a b u)*(c3_0 y z w a b u))+0)))))+(((-1)*(c4_3 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_3 y z w a b u))+((c5_1 y z w a b u)*(c6_2 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c1_0,c1_1,c1_2,c1_3,c2_0,c2_1,c2_2,c2_3,c3_0,c3_1,c3_2,c3_3,c4_3,c5_0,c5_1,c6_2,c6_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (y z w a b u : ℂ) :
    (certificate y z w a b u)[4]?=some 0 := by
  change some (((((c0_0 y z w a b u)*(c1_4 y z w a b u))+(((c0_1 y z w a b u)*(c1_3 y z w a b u))+(((c0_2 y z w a b u)*(c1_2 y z w a b u))+(((c0_3 y z w a b u)*(c1_1 y z w a b u))+(((c0_4 y z w a b u)*(c1_0 y z w a b u))+0)))))+(((c2_0 y z w a b u)*(c3_4 y z w a b u))+(((c2_1 y z w a b u)*(c3_3 y z w a b u))+(((c2_2 y z w a b u)*(c3_2 y z w a b u))+(((c2_3 y z w a b u)*(c3_1 y z w a b u))+(((c2_4 y z w a b u)*(c3_0 y z w a b u))+0))))))+(((-1)*(c4_4 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_4 y z w a b u))+((c5_1 y z w a b u)*(c6_3 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_0,c1_1,c1_2,c1_3,c1_4,c2_0,c2_1,c2_2,c2_3,c2_4,c3_0,c3_1,c3_2,c3_3,c3_4,c4_4,c5_0,c5_1,c6_3,c6_4]
  ring
#print axioms coefficient_4
theorem coefficient_5 (y z w a b u : ℂ) :
    (certificate y z w a b u)[5]?=some 0 := by
  change some (((((c0_0 y z w a b u)*(c1_5 y z w a b u))+(((c0_1 y z w a b u)*(c1_4 y z w a b u))+(((c0_2 y z w a b u)*(c1_3 y z w a b u))+(((c0_3 y z w a b u)*(c1_2 y z w a b u))+((c0_4 y z w a b u)*(c1_1 y z w a b u))))))+(((c2_0 y z w a b u)*(c3_5 y z w a b u))+(((c2_1 y z w a b u)*(c3_4 y z w a b u))+(((c2_2 y z w a b u)*(c3_3 y z w a b u))+(((c2_3 y z w a b u)*(c3_2 y z w a b u))+((c2_4 y z w a b u)*(c3_1 y z w a b u)))))))+(((-1)*(c4_5 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_5 y z w a b u))+((c5_1 y z w a b u)*(c6_4 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_1,c1_2,c1_3,c1_4,c1_5,c2_0,c2_1,c2_2,c2_3,c2_4,c3_1,c3_2,c3_3,c3_4,c3_5,c4_5,c5_0,c5_1,c6_4,c6_5]
  ring
#print axioms coefficient_5

theorem coefficient_6 (y z w a b u : ℂ) :
    (certificate y z w a b u)[6]?=some 0 := by
  change some (((((c0_0 y z w a b u)*(c1_6 y z w a b u))+(((c0_1 y z w a b u)*(c1_5 y z w a b u))+(((c0_2 y z w a b u)*(c1_4 y z w a b u))+(((c0_3 y z w a b u)*(c1_3 y z w a b u))+((c0_4 y z w a b u)*(c1_2 y z w a b u))))))+(((c2_0 y z w a b u)*(c3_6 y z w a b u))+(((c2_1 y z w a b u)*(c3_5 y z w a b u))+(((c2_2 y z w a b u)*(c3_4 y z w a b u))+(((c2_3 y z w a b u)*(c3_3 y z w a b u))+((c2_4 y z w a b u)*(c3_2 y z w a b u)))))))+(((-1)*(c4_6 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_6 y z w a b u))+((c5_1 y z w a b u)*(c6_5 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_2,c1_3,c1_4,c1_5,c1_6,c2_0,c2_1,c2_2,c2_3,c2_4,c3_2,c3_3,c3_4,c3_5,c3_6,c4_6,c5_0,c5_1,c6_5,c6_6]
  ring
#print axioms coefficient_6
theorem coefficient_7 (y z w a b u : ℂ) :
    (certificate y z w a b u)[7]?=some 0 := by
  change some (((((c0_0 y z w a b u)*(c1_7 y z w a b u))+(((c0_1 y z w a b u)*(c1_6 y z w a b u))+(((c0_2 y z w a b u)*(c1_5 y z w a b u))+(((c0_3 y z w a b u)*(c1_4 y z w a b u))+((c0_4 y z w a b u)*(c1_3 y z w a b u))))))+(((c2_0 y z w a b u)*(c3_7 y z w a b u))+(((c2_1 y z w a b u)*(c3_6 y z w a b u))+(((c2_2 y z w a b u)*(c3_5 y z w a b u))+(((c2_3 y z w a b u)*(c3_4 y z w a b u))+((c2_4 y z w a b u)*(c3_3 y z w a b u)))))))+(((-1)*(c4_7 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_7 y z w a b u))+((c5_1 y z w a b u)*(c6_6 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_3,c1_4,c1_5,c1_6,c1_7,c2_0,c2_1,c2_2,c2_3,c2_4,c3_3,c3_4,c3_5,c3_6,c3_7,c4_7,c5_0,c5_1,c6_6,c6_7]
  ring
#print axioms coefficient_7

theorem coefficient_8 (y z w a b u : ℂ) :
    (certificate y z w a b u)[8]?=some 0 := by
  change some (((((c0_0 y z w a b u)*(c1_8 y z w a b u))+(((c0_1 y z w a b u)*(c1_7 y z w a b u))+(((c0_2 y z w a b u)*(c1_6 y z w a b u))+(((c0_3 y z w a b u)*(c1_5 y z w a b u))+((c0_4 y z w a b u)*(c1_4 y z w a b u))))))+(((c2_0 y z w a b u)*(c3_8 y z w a b u))+(((c2_1 y z w a b u)*(c3_7 y z w a b u))+(((c2_2 y z w a b u)*(c3_6 y z w a b u))+(((c2_3 y z w a b u)*(c3_5 y z w a b u))+((c2_4 y z w a b u)*(c3_4 y z w a b u)))))))+(((-1)*(c4_8 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_8 y z w a b u))+((c5_1 y z w a b u)*(c6_7 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_4,c1_5,c1_6,c1_7,c1_8,c2_0,c2_1,c2_2,c2_3,c2_4,c3_4,c3_5,c3_6,c3_7,c3_8,c4_8,c5_0,c5_1,c6_7,c6_8]
  ring
#print axioms coefficient_8
theorem coefficient_9 (y z w a b u : ℂ) :
    (certificate y z w a b u)[9]?=some 0 := by
  change some (((((c0_0 y z w a b u)*(c1_9 y z w a b u))+(((c0_1 y z w a b u)*(c1_8 y z w a b u))+(((c0_2 y z w a b u)*(c1_7 y z w a b u))+(((c0_3 y z w a b u)*(c1_6 y z w a b u))+((c0_4 y z w a b u)*(c1_5 y z w a b u))))))+(((c2_0 y z w a b u)*(c3_9 y z w a b u))+(((c2_1 y z w a b u)*(c3_8 y z w a b u))+(((c2_2 y z w a b u)*(c3_7 y z w a b u))+(((c2_3 y z w a b u)*(c3_6 y z w a b u))+((c2_4 y z w a b u)*(c3_5 y z w a b u)))))))+(((-1)*(c4_9 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_9 y z w a b u))+((c5_1 y z w a b u)*(c6_8 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_5,c1_6,c1_7,c1_8,c1_9,c2_0,c2_1,c2_2,c2_3,c2_4,c3_5,c3_6,c3_7,c3_8,c3_9,c4_9,c5_0,c5_1,c6_8,c6_9]
  ring
#print axioms coefficient_9

theorem coefficient_10 (y z w a b u : ℂ) :
    (certificate y z w a b u)[10]?=some 0 := by
  change some (((((c0_0 y z w a b u)*(c1_10 y z w a b u))+(((c0_1 y z w a b u)*(c1_9 y z w a b u))+(((c0_2 y z w a b u)*(c1_8 y z w a b u))+(((c0_3 y z w a b u)*(c1_7 y z w a b u))+((c0_4 y z w a b u)*(c1_6 y z w a b u))))))+(((c2_0 y z w a b u)*(c3_10 y z w a b u))+(((c2_1 y z w a b u)*(c3_9 y z w a b u))+(((c2_2 y z w a b u)*(c3_8 y z w a b u))+(((c2_3 y z w a b u)*(c3_7 y z w a b u))+((c2_4 y z w a b u)*(c3_6 y z w a b u)))))))+(((-1)*(c4_10 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_10 y z w a b u))+((c5_1 y z w a b u)*(c6_9 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_10,c1_6,c1_7,c1_8,c1_9,c2_0,c2_1,c2_2,c2_3,c2_4,c3_10,c3_6,c3_7,c3_8,c3_9,c4_10,c5_0,c5_1,c6_10,c6_9]
  ring
#print axioms coefficient_10
theorem coefficient_11 (y z w a b u : ℂ) :
    (certificate y z w a b u)[11]?=some 0 := by
  change some (((((c0_0 y z w a b u)*(c1_11 y z w a b u))+(((c0_1 y z w a b u)*(c1_10 y z w a b u))+(((c0_2 y z w a b u)*(c1_9 y z w a b u))+(((c0_3 y z w a b u)*(c1_8 y z w a b u))+((c0_4 y z w a b u)*(c1_7 y z w a b u))))))+(((c2_0 y z w a b u)*(c3_11 y z w a b u))+(((c2_1 y z w a b u)*(c3_10 y z w a b u))+(((c2_2 y z w a b u)*(c3_9 y z w a b u))+(((c2_3 y z w a b u)*(c3_8 y z w a b u))+((c2_4 y z w a b u)*(c3_7 y z w a b u)))))))+(((-1)*(c4_11 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_11 y z w a b u))+((c5_1 y z w a b u)*(c6_10 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_10,c1_11,c1_7,c1_8,c1_9,c2_0,c2_1,c2_2,c2_3,c2_4,c3_10,c3_11,c3_7,c3_8,c3_9,c4_11,c5_0,c5_1,c6_10,c6_11]
  ring
#print axioms coefficient_11

theorem coefficient_12 (y z w a b u : ℂ) :
    (certificate y z w a b u)[12]?=some 0 := by
  change some (((((c0_0 y z w a b u)*(c1_12 y z w a b u))+(((c0_1 y z w a b u)*(c1_11 y z w a b u))+(((c0_2 y z w a b u)*(c1_10 y z w a b u))+(((c0_3 y z w a b u)*(c1_9 y z w a b u))+((c0_4 y z w a b u)*(c1_8 y z w a b u))))))+(((c2_0 y z w a b u)*(c3_12 y z w a b u))+(((c2_1 y z w a b u)*(c3_11 y z w a b u))+(((c2_2 y z w a b u)*(c3_10 y z w a b u))+(((c2_3 y z w a b u)*(c3_9 y z w a b u))+((c2_4 y z w a b u)*(c3_8 y z w a b u)))))))+(((-1)*(c4_12 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_12 y z w a b u))+((c5_1 y z w a b u)*(c6_11 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c0_2,c0_3,c0_4,c1_10,c1_11,c1_12,c1_8,c1_9,c2_0,c2_1,c2_2,c2_3,c2_4,c3_10,c3_11,c3_12,c3_8,c3_9,c4_12,c5_0,c5_1,c6_11,c6_12]
  ring
#print axioms coefficient_12
theorem coefficient_13 (y z w a b u : ℂ) :
    (certificate y z w a b u)[13]?=some 0 := by
  change some (((((c0_1 y z w a b u)*(c1_12 y z w a b u))+(((c0_2 y z w a b u)*(c1_11 y z w a b u))+(((c0_3 y z w a b u)*(c1_10 y z w a b u))+((c0_4 y z w a b u)*(c1_9 y z w a b u)))))+(((c2_1 y z w a b u)*(c3_12 y z w a b u))+(((c2_2 y z w a b u)*(c3_11 y z w a b u))+(((c2_3 y z w a b u)*(c3_10 y z w a b u))+((c2_4 y z w a b u)*(c3_9 y z w a b u))))))+(((-1)*(c4_13 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_13 y z w a b u))+((c5_1 y z w a b u)*(c6_12 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_1,c0_2,c0_3,c0_4,c1_10,c1_11,c1_12,c1_9,c2_1,c2_2,c2_3,c2_4,c3_10,c3_11,c3_12,c3_9,c4_13,c5_0,c5_1,c6_12,c6_13]
  ring
#print axioms coefficient_13

theorem coefficient_14 (y z w a b u : ℂ) :
    (certificate y z w a b u)[14]?=some 0 := by
  change some (((((c0_2 y z w a b u)*(c1_12 y z w a b u))+(((c0_3 y z w a b u)*(c1_11 y z w a b u))+((c0_4 y z w a b u)*(c1_10 y z w a b u))))+(((c2_2 y z w a b u)*(c3_12 y z w a b u))+(((c2_3 y z w a b u)*(c3_11 y z w a b u))+((c2_4 y z w a b u)*(c3_10 y z w a b u)))))+(((-1)*(c4_14 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_14 y z w a b u))+((c5_1 y z w a b u)*(c6_13 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_2,c0_3,c0_4,c1_10,c1_11,c1_12,c2_2,c2_3,c2_4,c3_10,c3_11,c3_12,c4_14,c5_0,c5_1,c6_13,c6_14]
  ring
#print axioms coefficient_14
theorem coefficient_15 (y z w a b u : ℂ) :
    (certificate y z w a b u)[15]?=some 0 := by
  change some (((((c0_3 y z w a b u)*(c1_12 y z w a b u))+((c0_4 y z w a b u)*(c1_11 y z w a b u)))+(((c2_3 y z w a b u)*(c3_12 y z w a b u))+((c2_4 y z w a b u)*(c3_11 y z w a b u))))+(((-1)*(c4_15 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_15 y z w a b u))+((c5_1 y z w a b u)*(c6_14 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_3,c0_4,c1_11,c1_12,c2_3,c2_4,c3_11,c3_12,c4_15,c5_0,c5_1,c6_14,c6_15]
  ring
#print axioms coefficient_15

theorem coefficient_16 (y z w a b u : ℂ) :
    (certificate y z w a b u)[16]?=some 0 := by
  change some ((((c0_4 y z w a b u)*(c1_12 y z w a b u))+((c2_4 y z w a b u)*(c3_12 y z w a b u)))+(((-1)*(c4_16 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_16 y z w a b u))+((c5_1 y z w a b u)*(c6_15 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_4,c1_12,c2_4,c3_12,c4_16,c5_0,c5_1,c6_15,c6_16]
  ring
#print axioms coefficient_16
theorem coefficient_17 (y z w a b u : ℂ) :
    (certificate y z w a b u)[17]?=some 0 := by
  change some (((-1)*(c4_17 y z w a b u))+((-1)*((c5_1 y z w a b u)*(c6_16 y z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [c4_17,c5_1,c6_16]
  ring
#print axioms coefficient_17

end SmallLevelTwentySixPariSourcePivot87
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixPariSourcePivot8
open SmallLevelPolynomialCoefficientCertificate

theorem coefficient_0 (y z w a b u : ℂ) :
    (certificate y z w a b u)[0]?=some 0 := by
  change some (((((c0_0 y z w a b u)*(c1_0 y z w a b u))+0)+(((c2_0 y z w a b u)*(c3_0 y z w a b u))+0))+(((-1)*(c4_0 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_0 y z w a b u))+0))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c1_0,c2_0,c3_0,c4_0,c5_0,c6_0]
  ring
#print axioms coefficient_0
theorem coefficient_1 (y z w a b u : ℂ) :
    (certificate y z w a b u)[1]?=some 0 := by
  change some (((((c0_0 y z w a b u)*(c1_1 y z w a b u))+(((c0_1 y z w a b u)*(c1_0 y z w a b u))+0))+(((c2_0 y z w a b u)*(c3_1 y z w a b u))+(((c2_1 y z w a b u)*(c3_0 y z w a b u))+0)))+(((-1)*(c4_1 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_1 y z w a b u))+(((c5_1 y z w a b u)*(c6_0 y z w a b u))+0)))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_0,c0_1,c1_0,c1_1,c2_0,c2_1,c3_0,c3_1,c4_1,c5_0,c5_1,c6_0,c6_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (y z w a b u : ℂ) :
    (certificate y z w a b u)[2]?=some 0 := by
  change some (((((c0_1 y z w a b u)*(c1_1 y z w a b u))+(((c0_2 y z w a b u)*(c1_0 y z w a b u))+0))+(((c2_1 y z w a b u)*(c3_1 y z w a b u))+(((c2_2 y z w a b u)*(c3_0 y z w a b u))+0)))+(((-1)*(c4_2 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_2 y z w a b u))+((c5_1 y z w a b u)*(c6_1 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_1,c0_2,c1_0,c1_1,c2_1,c2_2,c3_0,c3_1,c4_2,c5_0,c5_1,c6_1,c6_2]
  ring
#print axioms coefficient_2
theorem coefficient_3 (y z w a b u : ℂ) :
    (certificate y z w a b u)[3]?=some 0 := by
  change some (((((c0_2 y z w a b u)*(c1_1 y z w a b u))+(((c0_3 y z w a b u)*(c1_0 y z w a b u))+0))+(((c2_2 y z w a b u)*(c3_1 y z w a b u))+(((c2_3 y z w a b u)*(c3_0 y z w a b u))+0)))+(((-1)*(c4_3 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_3 y z w a b u))+((c5_1 y z w a b u)*(c6_2 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_2,c0_3,c1_0,c1_1,c2_2,c2_3,c3_0,c3_1,c4_3,c5_0,c5_1,c6_2,c6_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (y z w a b u : ℂ) :
    (certificate y z w a b u)[4]?=some 0 := by
  change some (((((c0_3 y z w a b u)*(c1_1 y z w a b u))+(((c0_4 y z w a b u)*(c1_0 y z w a b u))+0))+(((c2_3 y z w a b u)*(c3_1 y z w a b u))+(((c2_4 y z w a b u)*(c3_0 y z w a b u))+0)))+(((-1)*(c4_4 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_4 y z w a b u))+((c5_1 y z w a b u)*(c6_3 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_3,c0_4,c1_0,c1_1,c2_3,c2_4,c3_0,c3_1,c4_4,c5_0,c5_1,c6_3,c6_4]
  ring
#print axioms coefficient_4
theorem coefficient_5 (y z w a b u : ℂ) :
    (certificate y z w a b u)[5]?=some 0 := by
  change some ((((c0_4 y z w a b u)*(c1_1 y z w a b u))+((c2_4 y z w a b u)*(c3_1 y z w a b u)))+(((-1)*(c4_5 y z w a b u))+((-1)*(((c5_0 y z w a b u)*(c6_5 y z w a b u))+((c5_1 y z w a b u)*(c6_4 y z w a b u))))))=some (0:ℂ)
  apply congrArg some
  simp only [c0_4,c1_1,c2_4,c3_1,c4_5,c5_0,c5_1,c6_4,c6_5]
  ring
#print axioms coefficient_5

theorem coefficient_6 (y z w a b u : ℂ) :
    (certificate y z w a b u)[6]?=some 0 := by
  change some (((-1)*(c4_6 y z w a b u))+((-1)*((c5_1 y z w a b u)*(c6_5 y z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [c4_6,c5_1,c6_5]
  ring
#print axioms coefficient_6

end SmallLevelTwentySixPariSourcePivot8
end

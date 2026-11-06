module
public import SmallLevelTwentySixSourceIndexSplitIndexDataSeriesV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixSource89Split09
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89

theorem coefficient_0 (z w a b u : ℂ) : (innerCertificate z w a b u)[0]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_9_0 z w a b u))+0)+((((d0_1_0 z w a b u)*(d1_8_0 z w a b u))+0)+((((d0_2_0 z w a b u)*(d1_7_0 z w a b u))+0)+(((d0_3_0 z w a b u)*(d1_6_0 z w a b u))+0))))+((((d2_1_0 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_2_0 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_3_0 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_4_0 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_5_0 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_6_0 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_7_0 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_8_0 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_9_0 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+(((-1)*(d4_9_0 z w a b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_1_0,d0_2_0,d0_3_0,d1_6_0,d1_7_0,d1_8_0,d1_9_0,d2_1_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d2_7_0,d2_8_0,d2_9_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_9_0]
  ring
#print axioms coefficient_0

theorem coefficient_1 (z w a b u : ℂ) : (innerCertificate z w a b u)[1]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_9_1 z w a b u))+(((d0_0_1 z w a b u)*(d1_9_0 z w a b u))+0))+((((d0_1_0 z w a b u)*(d1_8_1 z w a b u))+(((d0_1_1 z w a b u)*(d1_8_0 z w a b u))+0))+((((d0_2_0 z w a b u)*(d1_7_1 z w a b u))+(((d0_2_1 z w a b u)*(d1_7_0 z w a b u))+0))+((d0_3_0 z w a b u)*(d1_6_1 z w a b u)))))+((((d2_1_1 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_2_1 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_3_1 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_4_1 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_5_1 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_6_1 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_7_1 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_8_1 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_9_1 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_9_1 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_6_1,d1_7_0,d1_7_1,d1_8_0,d1_8_1,d1_9_0,d1_9_1,d2_1_1,d2_2_1,d2_3_1,d2_4_1,d2_5_1,d2_6_1,d2_7_1,d2_8_1,d2_9_1,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_9_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (z w a b u : ℂ) : (innerCertificate z w a b u)[2]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_9_2 z w a b u))+((d0_0_1 z w a b u)*(d1_9_1 z w a b u)))+((((d0_1_0 z w a b u)*(d1_8_2 z w a b u))+((d0_1_1 z w a b u)*(d1_8_1 z w a b u)))+((((d0_2_0 z w a b u)*(d1_7_2 z w a b u))+((d0_2_1 z w a b u)*(d1_7_1 z w a b u)))+((d0_3_0 z w a b u)*(d1_6_2 z w a b u)))))+((((d2_1_2 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_2_2 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_3_2 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_4_2 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_5_2 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_6_2 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_7_2 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_8_2 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_9_2 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_9_2 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_6_2,d1_7_1,d1_7_2,d1_8_1,d1_8_2,d1_9_1,d1_9_2,d2_1_2,d2_2_2,d2_3_2,d2_4_2,d2_5_2,d2_6_2,d2_7_2,d2_8_2,d2_9_2,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_9_2]
  ring
#print axioms coefficient_2

theorem coefficient_3 (z w a b u : ℂ) : (innerCertificate z w a b u)[3]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_9_3 z w a b u))+((d0_0_1 z w a b u)*(d1_9_2 z w a b u)))+((((d0_1_0 z w a b u)*(d1_8_3 z w a b u))+((d0_1_1 z w a b u)*(d1_8_2 z w a b u)))+((((d0_2_0 z w a b u)*(d1_7_3 z w a b u))+((d0_2_1 z w a b u)*(d1_7_2 z w a b u)))+((d0_3_0 z w a b u)*(d1_6_3 z w a b u)))))+((((d2_1_3 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_2_3 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_3_3 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_4_3 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_5_3 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_6_3 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_7_3 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_8_3 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_9_3 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_9_3 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_6_3,d1_7_2,d1_7_3,d1_8_2,d1_8_3,d1_9_2,d1_9_3,d2_1_3,d2_2_3,d2_3_3,d2_4_3,d2_5_3,d2_6_3,d2_7_3,d2_8_3,d2_9_3,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_9_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (z w a b u : ℂ) : (innerCertificate z w a b u)[4]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_9_4 z w a b u))+((d0_0_1 z w a b u)*(d1_9_3 z w a b u)))+((((d0_1_0 z w a b u)*(d1_8_4 z w a b u))+((d0_1_1 z w a b u)*(d1_8_3 z w a b u)))+((((d0_2_0 z w a b u)*(d1_7_4 z w a b u))+((d0_2_1 z w a b u)*(d1_7_3 z w a b u)))+((d0_3_0 z w a b u)*(d1_6_4 z w a b u)))))+((((d2_1_4 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_2_4 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_3_4 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_4_4 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_5_4 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_6_4 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_7_4 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_8_4 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_9_4 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_9_4 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_6_4,d1_7_3,d1_7_4,d1_8_3,d1_8_4,d1_9_3,d1_9_4,d2_1_4,d2_2_4,d2_3_4,d2_4_4,d2_5_4,d2_6_4,d2_7_4,d2_8_4,d2_9_4,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_9_4]
  ring
#print axioms coefficient_4

theorem coefficient_5 (z w a b u : ℂ) : (innerCertificate z w a b u)[5]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_9_5 z w a b u))+((d0_0_1 z w a b u)*(d1_9_4 z w a b u)))+((((d0_1_0 z w a b u)*(d1_8_5 z w a b u))+((d0_1_1 z w a b u)*(d1_8_4 z w a b u)))+((((d0_2_0 z w a b u)*(d1_7_5 z w a b u))+((d0_2_1 z w a b u)*(d1_7_4 z w a b u)))+((d0_3_0 z w a b u)*(d1_6_5 z w a b u)))))+((((d2_1_5 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_2_5 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_3_5 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_4_5 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_5_5 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_6_5 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_7_5 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_8_5 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_9_5 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_9_5 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_6_5,d1_7_4,d1_7_5,d1_8_4,d1_8_5,d1_9_4,d1_9_5,d2_1_5,d2_2_5,d2_3_5,d2_4_5,d2_5_5,d2_6_5,d2_7_5,d2_8_5,d2_9_5,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_9_5]
  ring
#print axioms coefficient_5

theorem coefficient_6 (z w a b u : ℂ) : (innerCertificate z w a b u)[6]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_9_6 z w a b u))+((d0_0_1 z w a b u)*(d1_9_5 z w a b u)))+((((d0_1_0 z w a b u)*(d1_8_6 z w a b u))+((d0_1_1 z w a b u)*(d1_8_5 z w a b u)))+((((d0_2_0 z w a b u)*(d1_7_6 z w a b u))+((d0_2_1 z w a b u)*(d1_7_5 z w a b u)))+((d0_3_0 z w a b u)*(d1_6_6 z w a b u)))))+((((d2_1_6 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_2_6 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_3_6 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_4_6 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_5_6 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_6_6 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_7_6 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_8_6 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_9_6 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_9_6 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_6_6,d1_7_5,d1_7_6,d1_8_5,d1_8_6,d1_9_5,d1_9_6,d2_1_6,d2_2_6,d2_3_6,d2_4_6,d2_5_6,d2_6_6,d2_7_6,d2_8_6,d2_9_6,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_9_6]
  ring
#print axioms coefficient_6

theorem coefficient_7 (z w a b u : ℂ) : (innerCertificate z w a b u)[7]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_9_7 z w a b u))+((d0_0_1 z w a b u)*(d1_9_6 z w a b u)))+((((d0_1_0 z w a b u)*(d1_8_7 z w a b u))+((d0_1_1 z w a b u)*(d1_8_6 z w a b u)))+((((d0_2_0 z w a b u)*(d1_7_7 z w a b u))+((d0_2_1 z w a b u)*(d1_7_6 z w a b u)))+((d0_3_0 z w a b u)*(d1_6_7 z w a b u)))))+((((d2_1_7 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_2_7 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_3_7 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_4_7 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_5_7 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_6_7 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_7_7 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_8_7 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_9_7 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_9_7 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_6_7,d1_7_6,d1_7_7,d1_8_6,d1_8_7,d1_9_6,d1_9_7,d2_1_7,d2_2_7,d2_3_7,d2_4_7,d2_5_7,d2_6_7,d2_7_7,d2_8_7,d2_9_7,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_9_7]
  ring
#print axioms coefficient_7

theorem coefficient_8 (z w a b u : ℂ) : (innerCertificate z w a b u)[8]?=some 0 := by
  change some (((((d0_0_1 z w a b u)*(d1_9_7 z w a b u))+(((d0_1_1 z w a b u)*(d1_8_7 z w a b u))+((d0_2_1 z w a b u)*(d1_7_7 z w a b u))))+((-1)*(d4_9_8 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_1,d0_1_1,d0_2_1,d1_7_7,d1_8_7,d1_9_7,d4_9_8]
  ring
#print axioms coefficient_8

end SmallLevelTwentySixSource89Split09
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixSource89Split10
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89

theorem coefficient_0 (z w a b u : ℂ) : (innerCertificate z w a b u)[0]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_10_0 z w a b u))+0)+((((d0_1_0 z w a b u)*(d1_9_0 z w a b u))+0)+((((d0_2_0 z w a b u)*(d1_8_0 z w a b u))+0)+(((d0_3_0 z w a b u)*(d1_7_0 z w a b u))+0))))+((((d2_2_0 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_3_0 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_4_0 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_5_0 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_6_0 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_7_0 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_8_0 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_9_0 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_10_0 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+(((-1)*(d4_10_0 z w a b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_1_0,d0_2_0,d0_3_0,d1_10_0,d1_7_0,d1_8_0,d1_9_0,d2_10_0,d2_2_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d2_7_0,d2_8_0,d2_9_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_10_0]
  ring
#print axioms coefficient_0

theorem coefficient_1 (z w a b u : ℂ) : (innerCertificate z w a b u)[1]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_10_1 z w a b u))+(((d0_0_1 z w a b u)*(d1_10_0 z w a b u))+0))+((((d0_1_0 z w a b u)*(d1_9_1 z w a b u))+(((d0_1_1 z w a b u)*(d1_9_0 z w a b u))+0))+((((d0_2_0 z w a b u)*(d1_8_1 z w a b u))+(((d0_2_1 z w a b u)*(d1_8_0 z w a b u))+0))+((d0_3_0 z w a b u)*(d1_7_1 z w a b u)))))+((((d2_2_1 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_3_1 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_4_1 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_5_1 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_6_1 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_7_1 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_8_1 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_9_1 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_10_1 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_10_1 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_0,d1_10_1,d1_7_1,d1_8_0,d1_8_1,d1_9_0,d1_9_1,d2_10_1,d2_2_1,d2_3_1,d2_4_1,d2_5_1,d2_6_1,d2_7_1,d2_8_1,d2_9_1,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_10_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (z w a b u : ℂ) : (innerCertificate z w a b u)[2]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_10_2 z w a b u))+((d0_0_1 z w a b u)*(d1_10_1 z w a b u)))+((((d0_1_0 z w a b u)*(d1_9_2 z w a b u))+((d0_1_1 z w a b u)*(d1_9_1 z w a b u)))+((((d0_2_0 z w a b u)*(d1_8_2 z w a b u))+((d0_2_1 z w a b u)*(d1_8_1 z w a b u)))+((d0_3_0 z w a b u)*(d1_7_2 z w a b u)))))+((((d2_2_2 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_3_2 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_4_2 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_5_2 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_6_2 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_7_2 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_8_2 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_9_2 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_10_2 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_10_2 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_1,d1_10_2,d1_7_2,d1_8_1,d1_8_2,d1_9_1,d1_9_2,d2_10_2,d2_2_2,d2_3_2,d2_4_2,d2_5_2,d2_6_2,d2_7_2,d2_8_2,d2_9_2,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_10_2]
  ring
#print axioms coefficient_2

theorem coefficient_3 (z w a b u : ℂ) : (innerCertificate z w a b u)[3]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_10_3 z w a b u))+((d0_0_1 z w a b u)*(d1_10_2 z w a b u)))+((((d0_1_0 z w a b u)*(d1_9_3 z w a b u))+((d0_1_1 z w a b u)*(d1_9_2 z w a b u)))+((((d0_2_0 z w a b u)*(d1_8_3 z w a b u))+((d0_2_1 z w a b u)*(d1_8_2 z w a b u)))+((d0_3_0 z w a b u)*(d1_7_3 z w a b u)))))+((((d2_2_3 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_3_3 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_4_3 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_5_3 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_6_3 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_7_3 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_8_3 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_9_3 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_10_3 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_10_3 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_2,d1_10_3,d1_7_3,d1_8_2,d1_8_3,d1_9_2,d1_9_3,d2_10_3,d2_2_3,d2_3_3,d2_4_3,d2_5_3,d2_6_3,d2_7_3,d2_8_3,d2_9_3,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_10_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (z w a b u : ℂ) : (innerCertificate z w a b u)[4]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_10_4 z w a b u))+((d0_0_1 z w a b u)*(d1_10_3 z w a b u)))+((((d0_1_0 z w a b u)*(d1_9_4 z w a b u))+((d0_1_1 z w a b u)*(d1_9_3 z w a b u)))+((((d0_2_0 z w a b u)*(d1_8_4 z w a b u))+((d0_2_1 z w a b u)*(d1_8_3 z w a b u)))+((d0_3_0 z w a b u)*(d1_7_4 z w a b u)))))+((((d2_2_4 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_3_4 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_4_4 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_5_4 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_6_4 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_7_4 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_8_4 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_9_4 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_10_4 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_10_4 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_3,d1_10_4,d1_7_4,d1_8_3,d1_8_4,d1_9_3,d1_9_4,d2_10_4,d2_2_4,d2_3_4,d2_4_4,d2_5_4,d2_6_4,d2_7_4,d2_8_4,d2_9_4,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_10_4]
  ring
#print axioms coefficient_4

theorem coefficient_5 (z w a b u : ℂ) : (innerCertificate z w a b u)[5]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_10_5 z w a b u))+((d0_0_1 z w a b u)*(d1_10_4 z w a b u)))+((((d0_1_0 z w a b u)*(d1_9_5 z w a b u))+((d0_1_1 z w a b u)*(d1_9_4 z w a b u)))+((((d0_2_0 z w a b u)*(d1_8_5 z w a b u))+((d0_2_1 z w a b u)*(d1_8_4 z w a b u)))+((d0_3_0 z w a b u)*(d1_7_5 z w a b u)))))+((((d2_2_5 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_3_5 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_4_5 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_5_5 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_6_5 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_7_5 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_8_5 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_9_5 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_10_5 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_10_5 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_4,d1_10_5,d1_7_5,d1_8_4,d1_8_5,d1_9_4,d1_9_5,d2_10_5,d2_2_5,d2_3_5,d2_4_5,d2_5_5,d2_6_5,d2_7_5,d2_8_5,d2_9_5,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_10_5]
  ring
#print axioms coefficient_5

theorem coefficient_6 (z w a b u : ℂ) : (innerCertificate z w a b u)[6]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_10_6 z w a b u))+((d0_0_1 z w a b u)*(d1_10_5 z w a b u)))+((((d0_1_0 z w a b u)*(d1_9_6 z w a b u))+((d0_1_1 z w a b u)*(d1_9_5 z w a b u)))+((((d0_2_0 z w a b u)*(d1_8_6 z w a b u))+((d0_2_1 z w a b u)*(d1_8_5 z w a b u)))+((d0_3_0 z w a b u)*(d1_7_6 z w a b u)))))+((((d2_2_6 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_3_6 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_4_6 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_5_6 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_6_6 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_7_6 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_8_6 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_9_6 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_10_6 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_10_6 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_5,d1_10_6,d1_7_6,d1_8_5,d1_8_6,d1_9_5,d1_9_6,d2_10_6,d2_2_6,d2_3_6,d2_4_6,d2_5_6,d2_6_6,d2_7_6,d2_8_6,d2_9_6,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_10_6]
  ring
#print axioms coefficient_6

theorem coefficient_7 (z w a b u : ℂ) : (innerCertificate z w a b u)[7]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_10_7 z w a b u))+((d0_0_1 z w a b u)*(d1_10_6 z w a b u)))+((((d0_1_0 z w a b u)*(d1_9_7 z w a b u))+((d0_1_1 z w a b u)*(d1_9_6 z w a b u)))+((((d0_2_0 z w a b u)*(d1_8_7 z w a b u))+((d0_2_1 z w a b u)*(d1_8_6 z w a b u)))+((d0_3_0 z w a b u)*(d1_7_7 z w a b u)))))+((((d2_2_7 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_3_7 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_4_7 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_5_7 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_6_7 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_7_7 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_8_7 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_9_7 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_10_7 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_10_7 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_6,d1_10_7,d1_7_7,d1_8_6,d1_8_7,d1_9_6,d1_9_7,d2_10_7,d2_2_7,d2_3_7,d2_4_7,d2_5_7,d2_6_7,d2_7_7,d2_8_7,d2_9_7,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_10_7]
  ring
#print axioms coefficient_7

theorem coefficient_8 (z w a b u : ℂ) : (innerCertificate z w a b u)[8]?=some 0 := by
  change some (((((d0_0_1 z w a b u)*(d1_10_7 z w a b u))+(((d0_1_1 z w a b u)*(d1_9_7 z w a b u))+((d0_2_1 z w a b u)*(d1_8_7 z w a b u))))+((-1)*(d4_10_8 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_1,d0_1_1,d0_2_1,d1_10_7,d1_8_7,d1_9_7,d4_10_8]
  ring
#print axioms coefficient_8

end SmallLevelTwentySixSource89Split10
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixSource89Split11
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89

theorem coefficient_0 (z w a b u : ℂ) : (innerCertificate z w a b u)[0]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_11_0 z w a b u))+0)+((((d0_1_0 z w a b u)*(d1_10_0 z w a b u))+0)+((((d0_2_0 z w a b u)*(d1_9_0 z w a b u))+0)+(((d0_3_0 z w a b u)*(d1_8_0 z w a b u))+0))))+((((d2_3_0 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_4_0 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_5_0 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_6_0 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_7_0 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_8_0 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_9_0 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_10_0 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_11_0 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+(((-1)*(d4_11_0 z w a b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_1_0,d0_2_0,d0_3_0,d1_10_0,d1_11_0,d1_8_0,d1_9_0,d2_10_0,d2_11_0,d2_3_0,d2_4_0,d2_5_0,d2_6_0,d2_7_0,d2_8_0,d2_9_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_11_0]
  ring
#print axioms coefficient_0

theorem coefficient_1 (z w a b u : ℂ) : (innerCertificate z w a b u)[1]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_11_1 z w a b u))+(((d0_0_1 z w a b u)*(d1_11_0 z w a b u))+0))+((((d0_1_0 z w a b u)*(d1_10_1 z w a b u))+(((d0_1_1 z w a b u)*(d1_10_0 z w a b u))+0))+((((d0_2_0 z w a b u)*(d1_9_1 z w a b u))+(((d0_2_1 z w a b u)*(d1_9_0 z w a b u))+0))+((d0_3_0 z w a b u)*(d1_8_1 z w a b u)))))+((((d2_3_1 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_4_1 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_5_1 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_6_1 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_7_1 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_8_1 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_9_1 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_10_1 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_11_1 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_11_1 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_0,d1_10_1,d1_11_0,d1_11_1,d1_8_1,d1_9_0,d1_9_1,d2_10_1,d2_11_1,d2_3_1,d2_4_1,d2_5_1,d2_6_1,d2_7_1,d2_8_1,d2_9_1,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_11_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (z w a b u : ℂ) : (innerCertificate z w a b u)[2]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_11_2 z w a b u))+((d0_0_1 z w a b u)*(d1_11_1 z w a b u)))+((((d0_1_0 z w a b u)*(d1_10_2 z w a b u))+((d0_1_1 z w a b u)*(d1_10_1 z w a b u)))+((((d0_2_0 z w a b u)*(d1_9_2 z w a b u))+((d0_2_1 z w a b u)*(d1_9_1 z w a b u)))+((d0_3_0 z w a b u)*(d1_8_2 z w a b u)))))+((((d2_3_2 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_4_2 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_5_2 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_6_2 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_7_2 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_8_2 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_9_2 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_10_2 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_11_2 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_11_2 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_1,d1_10_2,d1_11_1,d1_11_2,d1_8_2,d1_9_1,d1_9_2,d2_10_2,d2_11_2,d2_3_2,d2_4_2,d2_5_2,d2_6_2,d2_7_2,d2_8_2,d2_9_2,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_11_2]
  ring
#print axioms coefficient_2

theorem coefficient_3 (z w a b u : ℂ) : (innerCertificate z w a b u)[3]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_11_3 z w a b u))+((d0_0_1 z w a b u)*(d1_11_2 z w a b u)))+((((d0_1_0 z w a b u)*(d1_10_3 z w a b u))+((d0_1_1 z w a b u)*(d1_10_2 z w a b u)))+((((d0_2_0 z w a b u)*(d1_9_3 z w a b u))+((d0_2_1 z w a b u)*(d1_9_2 z w a b u)))+((d0_3_0 z w a b u)*(d1_8_3 z w a b u)))))+((((d2_3_3 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_4_3 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_5_3 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_6_3 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_7_3 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_8_3 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_9_3 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_10_3 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_11_3 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_11_3 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_2,d1_10_3,d1_11_2,d1_11_3,d1_8_3,d1_9_2,d1_9_3,d2_10_3,d2_11_3,d2_3_3,d2_4_3,d2_5_3,d2_6_3,d2_7_3,d2_8_3,d2_9_3,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_11_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (z w a b u : ℂ) : (innerCertificate z w a b u)[4]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_11_4 z w a b u))+((d0_0_1 z w a b u)*(d1_11_3 z w a b u)))+((((d0_1_0 z w a b u)*(d1_10_4 z w a b u))+((d0_1_1 z w a b u)*(d1_10_3 z w a b u)))+((((d0_2_0 z w a b u)*(d1_9_4 z w a b u))+((d0_2_1 z w a b u)*(d1_9_3 z w a b u)))+((d0_3_0 z w a b u)*(d1_8_4 z w a b u)))))+((((d2_3_4 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_4_4 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_5_4 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_6_4 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_7_4 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_8_4 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_9_4 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_10_4 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_11_4 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_11_4 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_3,d1_10_4,d1_11_3,d1_11_4,d1_8_4,d1_9_3,d1_9_4,d2_10_4,d2_11_4,d2_3_4,d2_4_4,d2_5_4,d2_6_4,d2_7_4,d2_8_4,d2_9_4,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_11_4]
  ring
#print axioms coefficient_4

theorem coefficient_5 (z w a b u : ℂ) : (innerCertificate z w a b u)[5]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_11_5 z w a b u))+((d0_0_1 z w a b u)*(d1_11_4 z w a b u)))+((((d0_1_0 z w a b u)*(d1_10_5 z w a b u))+((d0_1_1 z w a b u)*(d1_10_4 z w a b u)))+((((d0_2_0 z w a b u)*(d1_9_5 z w a b u))+((d0_2_1 z w a b u)*(d1_9_4 z w a b u)))+((d0_3_0 z w a b u)*(d1_8_5 z w a b u)))))+((((d2_3_5 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_4_5 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_5_5 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_6_5 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_7_5 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_8_5 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_9_5 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_10_5 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_11_5 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_11_5 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_4,d1_10_5,d1_11_4,d1_11_5,d1_8_5,d1_9_4,d1_9_5,d2_10_5,d2_11_5,d2_3_5,d2_4_5,d2_5_5,d2_6_5,d2_7_5,d2_8_5,d2_9_5,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_11_5]
  ring
#print axioms coefficient_5

theorem coefficient_6 (z w a b u : ℂ) : (innerCertificate z w a b u)[6]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_11_6 z w a b u))+((d0_0_1 z w a b u)*(d1_11_5 z w a b u)))+((((d0_1_0 z w a b u)*(d1_10_6 z w a b u))+((d0_1_1 z w a b u)*(d1_10_5 z w a b u)))+((((d0_2_0 z w a b u)*(d1_9_6 z w a b u))+((d0_2_1 z w a b u)*(d1_9_5 z w a b u)))+((d0_3_0 z w a b u)*(d1_8_6 z w a b u)))))+((((d2_3_6 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_4_6 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_5_6 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_6_6 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_7_6 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_8_6 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_9_6 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_10_6 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_11_6 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_11_6 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_5,d1_10_6,d1_11_5,d1_11_6,d1_8_6,d1_9_5,d1_9_6,d2_10_6,d2_11_6,d2_3_6,d2_4_6,d2_5_6,d2_6_6,d2_7_6,d2_8_6,d2_9_6,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_11_6]
  ring
#print axioms coefficient_6

theorem coefficient_7 (z w a b u : ℂ) : (innerCertificate z w a b u)[7]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_11_7 z w a b u))+((d0_0_1 z w a b u)*(d1_11_6 z w a b u)))+((((d0_1_0 z w a b u)*(d1_10_7 z w a b u))+((d0_1_1 z w a b u)*(d1_10_6 z w a b u)))+((((d0_2_0 z w a b u)*(d1_9_7 z w a b u))+((d0_2_1 z w a b u)*(d1_9_6 z w a b u)))+((d0_3_0 z w a b u)*(d1_8_7 z w a b u)))))+((((d2_3_7 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_4_7 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_5_7 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_6_7 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_7_7 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_8_7 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_9_7 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_10_7 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_11_7 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_11_7 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_6,d1_10_7,d1_11_6,d1_11_7,d1_8_7,d1_9_6,d1_9_7,d2_10_7,d2_11_7,d2_3_7,d2_4_7,d2_5_7,d2_6_7,d2_7_7,d2_8_7,d2_9_7,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_11_7]
  ring
#print axioms coefficient_7

theorem coefficient_8 (z w a b u : ℂ) : (innerCertificate z w a b u)[8]?=some 0 := by
  change some (((((d0_0_1 z w a b u)*(d1_11_7 z w a b u))+(((d0_1_1 z w a b u)*(d1_10_7 z w a b u))+((d0_2_1 z w a b u)*(d1_9_7 z w a b u))))+((-1)*(d4_11_8 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_1,d0_1_1,d0_2_1,d1_10_7,d1_11_7,d1_9_7,d4_11_8]
  ring
#print axioms coefficient_8

end SmallLevelTwentySixSource89Split11
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixSource89Split12
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89

theorem coefficient_0 (z w a b u : ℂ) : (innerCertificate z w a b u)[0]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_12_0 z w a b u))+0)+((((d0_1_0 z w a b u)*(d1_11_0 z w a b u))+0)+((((d0_2_0 z w a b u)*(d1_10_0 z w a b u))+0)+(((d0_3_0 z w a b u)*(d1_9_0 z w a b u))+0))))+((((d2_4_0 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_5_0 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_6_0 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_7_0 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_8_0 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_9_0 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_10_0 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_11_0 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_12_0 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+(((-1)*(d4_12_0 z w a b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_1_0,d0_2_0,d0_3_0,d1_10_0,d1_11_0,d1_12_0,d1_9_0,d2_10_0,d2_11_0,d2_12_0,d2_4_0,d2_5_0,d2_6_0,d2_7_0,d2_8_0,d2_9_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_12_0]
  ring
#print axioms coefficient_0

theorem coefficient_1 (z w a b u : ℂ) : (innerCertificate z w a b u)[1]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_12_1 z w a b u))+(((d0_0_1 z w a b u)*(d1_12_0 z w a b u))+0))+((((d0_1_0 z w a b u)*(d1_11_1 z w a b u))+(((d0_1_1 z w a b u)*(d1_11_0 z w a b u))+0))+((((d0_2_0 z w a b u)*(d1_10_1 z w a b u))+(((d0_2_1 z w a b u)*(d1_10_0 z w a b u))+0))+((d0_3_0 z w a b u)*(d1_9_1 z w a b u)))))+((((d2_4_1 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_5_1 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_6_1 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_7_1 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_8_1 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_9_1 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_10_1 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_11_1 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_12_1 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_12_1 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_0,d1_10_1,d1_11_0,d1_11_1,d1_12_0,d1_12_1,d1_9_1,d2_10_1,d2_11_1,d2_12_1,d2_4_1,d2_5_1,d2_6_1,d2_7_1,d2_8_1,d2_9_1,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_12_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (z w a b u : ℂ) : (innerCertificate z w a b u)[2]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_12_2 z w a b u))+((d0_0_1 z w a b u)*(d1_12_1 z w a b u)))+((((d0_1_0 z w a b u)*(d1_11_2 z w a b u))+((d0_1_1 z w a b u)*(d1_11_1 z w a b u)))+((((d0_2_0 z w a b u)*(d1_10_2 z w a b u))+((d0_2_1 z w a b u)*(d1_10_1 z w a b u)))+((d0_3_0 z w a b u)*(d1_9_2 z w a b u)))))+((((d2_4_2 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_5_2 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_6_2 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_7_2 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_8_2 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_9_2 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_10_2 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_11_2 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_12_2 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_12_2 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_1,d1_10_2,d1_11_1,d1_11_2,d1_12_1,d1_12_2,d1_9_2,d2_10_2,d2_11_2,d2_12_2,d2_4_2,d2_5_2,d2_6_2,d2_7_2,d2_8_2,d2_9_2,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_12_2]
  ring
#print axioms coefficient_2

theorem coefficient_3 (z w a b u : ℂ) : (innerCertificate z w a b u)[3]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_12_3 z w a b u))+((d0_0_1 z w a b u)*(d1_12_2 z w a b u)))+((((d0_1_0 z w a b u)*(d1_11_3 z w a b u))+((d0_1_1 z w a b u)*(d1_11_2 z w a b u)))+((((d0_2_0 z w a b u)*(d1_10_3 z w a b u))+((d0_2_1 z w a b u)*(d1_10_2 z w a b u)))+((d0_3_0 z w a b u)*(d1_9_3 z w a b u)))))+((((d2_4_3 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_5_3 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_6_3 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_7_3 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_8_3 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_9_3 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_10_3 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_11_3 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_12_3 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_12_3 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_2,d1_10_3,d1_11_2,d1_11_3,d1_12_2,d1_12_3,d1_9_3,d2_10_3,d2_11_3,d2_12_3,d2_4_3,d2_5_3,d2_6_3,d2_7_3,d2_8_3,d2_9_3,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_12_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (z w a b u : ℂ) : (innerCertificate z w a b u)[4]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_12_4 z w a b u))+((d0_0_1 z w a b u)*(d1_12_3 z w a b u)))+((((d0_1_0 z w a b u)*(d1_11_4 z w a b u))+((d0_1_1 z w a b u)*(d1_11_3 z w a b u)))+((((d0_2_0 z w a b u)*(d1_10_4 z w a b u))+((d0_2_1 z w a b u)*(d1_10_3 z w a b u)))+((d0_3_0 z w a b u)*(d1_9_4 z w a b u)))))+((((d2_4_4 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_5_4 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_6_4 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_7_4 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_8_4 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_9_4 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_10_4 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_11_4 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_12_4 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_12_4 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_3,d1_10_4,d1_11_3,d1_11_4,d1_12_3,d1_12_4,d1_9_4,d2_10_4,d2_11_4,d2_12_4,d2_4_4,d2_5_4,d2_6_4,d2_7_4,d2_8_4,d2_9_4,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_12_4]
  ring
#print axioms coefficient_4

theorem coefficient_5 (z w a b u : ℂ) : (innerCertificate z w a b u)[5]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_12_5 z w a b u))+((d0_0_1 z w a b u)*(d1_12_4 z w a b u)))+((((d0_1_0 z w a b u)*(d1_11_5 z w a b u))+((d0_1_1 z w a b u)*(d1_11_4 z w a b u)))+((((d0_2_0 z w a b u)*(d1_10_5 z w a b u))+((d0_2_1 z w a b u)*(d1_10_4 z w a b u)))+((d0_3_0 z w a b u)*(d1_9_5 z w a b u)))))+((((d2_4_5 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_5_5 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_6_5 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_7_5 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_8_5 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_9_5 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_10_5 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_11_5 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_12_5 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_12_5 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_4,d1_10_5,d1_11_4,d1_11_5,d1_12_4,d1_12_5,d1_9_5,d2_10_5,d2_11_5,d2_12_5,d2_4_5,d2_5_5,d2_6_5,d2_7_5,d2_8_5,d2_9_5,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_12_5]
  ring
#print axioms coefficient_5

theorem coefficient_6 (z w a b u : ℂ) : (innerCertificate z w a b u)[6]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_12_6 z w a b u))+((d0_0_1 z w a b u)*(d1_12_5 z w a b u)))+((((d0_1_0 z w a b u)*(d1_11_6 z w a b u))+((d0_1_1 z w a b u)*(d1_11_5 z w a b u)))+((((d0_2_0 z w a b u)*(d1_10_6 z w a b u))+((d0_2_1 z w a b u)*(d1_10_5 z w a b u)))+((d0_3_0 z w a b u)*(d1_9_6 z w a b u)))))+((((d2_4_6 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_5_6 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_6_6 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_7_6 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_8_6 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_9_6 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_10_6 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_11_6 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_12_6 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_12_6 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_5,d1_10_6,d1_11_5,d1_11_6,d1_12_5,d1_12_6,d1_9_6,d2_10_6,d2_11_6,d2_12_6,d2_4_6,d2_5_6,d2_6_6,d2_7_6,d2_8_6,d2_9_6,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_12_6]
  ring
#print axioms coefficient_6

theorem coefficient_7 (z w a b u : ℂ) : (innerCertificate z w a b u)[7]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_12_7 z w a b u))+((d0_0_1 z w a b u)*(d1_12_6 z w a b u)))+((((d0_1_0 z w a b u)*(d1_11_7 z w a b u))+((d0_1_1 z w a b u)*(d1_11_6 z w a b u)))+((((d0_2_0 z w a b u)*(d1_10_7 z w a b u))+((d0_2_1 z w a b u)*(d1_10_6 z w a b u)))+((d0_3_0 z w a b u)*(d1_9_7 z w a b u)))))+((((d2_4_7 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_5_7 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_6_7 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_7_7 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_8_7 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_9_7 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_10_7 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_11_7 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_12_7 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_12_7 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_6,d1_10_7,d1_11_6,d1_11_7,d1_12_6,d1_12_7,d1_9_7,d2_10_7,d2_11_7,d2_12_7,d2_4_7,d2_5_7,d2_6_7,d2_7_7,d2_8_7,d2_9_7,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_12_7]
  ring
#print axioms coefficient_7

theorem coefficient_8 (z w a b u : ℂ) : (innerCertificate z w a b u)[8]?=some 0 := by
  change some (((((d0_0_1 z w a b u)*(d1_12_7 z w a b u))+(((d0_1_1 z w a b u)*(d1_11_7 z w a b u))+((d0_2_1 z w a b u)*(d1_10_7 z w a b u))))+((-1)*(d4_12_8 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_1,d0_1_1,d0_2_1,d1_10_7,d1_11_7,d1_12_7,d4_12_8]
  ring
#print axioms coefficient_8

end SmallLevelTwentySixSource89Split12
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixSource89Split13
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89

theorem coefficient_0 (z w a b u : ℂ) : (innerCertificate z w a b u)[0]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_13_0 z w a b u))+0)+((((d0_1_0 z w a b u)*(d1_12_0 z w a b u))+0)+((((d0_2_0 z w a b u)*(d1_11_0 z w a b u))+0)+(((d0_3_0 z w a b u)*(d1_10_0 z w a b u))+0))))+((((d2_5_0 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_6_0 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_7_0 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_8_0 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_9_0 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_10_0 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_11_0 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_12_0 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_13_0 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+(((-1)*(d4_13_0 z w a b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_1_0,d0_2_0,d0_3_0,d1_10_0,d1_11_0,d1_12_0,d1_13_0,d2_10_0,d2_11_0,d2_12_0,d2_13_0,d2_5_0,d2_6_0,d2_7_0,d2_8_0,d2_9_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_13_0]
  ring
#print axioms coefficient_0

theorem coefficient_1 (z w a b u : ℂ) : (innerCertificate z w a b u)[1]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_13_1 z w a b u))+(((d0_0_1 z w a b u)*(d1_13_0 z w a b u))+0))+((((d0_1_0 z w a b u)*(d1_12_1 z w a b u))+(((d0_1_1 z w a b u)*(d1_12_0 z w a b u))+0))+((((d0_2_0 z w a b u)*(d1_11_1 z w a b u))+(((d0_2_1 z w a b u)*(d1_11_0 z w a b u))+0))+((d0_3_0 z w a b u)*(d1_10_1 z w a b u)))))+((((d2_5_1 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_6_1 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_7_1 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_8_1 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_9_1 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_10_1 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_11_1 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_12_1 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_13_1 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_13_1 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_1,d1_11_0,d1_11_1,d1_12_0,d1_12_1,d1_13_0,d1_13_1,d2_10_1,d2_11_1,d2_12_1,d2_13_1,d2_5_1,d2_6_1,d2_7_1,d2_8_1,d2_9_1,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_13_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (z w a b u : ℂ) : (innerCertificate z w a b u)[2]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_13_2 z w a b u))+((d0_0_1 z w a b u)*(d1_13_1 z w a b u)))+((((d0_1_0 z w a b u)*(d1_12_2 z w a b u))+((d0_1_1 z w a b u)*(d1_12_1 z w a b u)))+((((d0_2_0 z w a b u)*(d1_11_2 z w a b u))+((d0_2_1 z w a b u)*(d1_11_1 z w a b u)))+((d0_3_0 z w a b u)*(d1_10_2 z w a b u)))))+((((d2_5_2 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_6_2 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_7_2 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_8_2 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_9_2 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_10_2 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_11_2 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_12_2 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_13_2 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_13_2 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_2,d1_11_1,d1_11_2,d1_12_1,d1_12_2,d1_13_1,d1_13_2,d2_10_2,d2_11_2,d2_12_2,d2_13_2,d2_5_2,d2_6_2,d2_7_2,d2_8_2,d2_9_2,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_13_2]
  ring
#print axioms coefficient_2

theorem coefficient_3 (z w a b u : ℂ) : (innerCertificate z w a b u)[3]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_13_3 z w a b u))+((d0_0_1 z w a b u)*(d1_13_2 z w a b u)))+((((d0_1_0 z w a b u)*(d1_12_3 z w a b u))+((d0_1_1 z w a b u)*(d1_12_2 z w a b u)))+((((d0_2_0 z w a b u)*(d1_11_3 z w a b u))+((d0_2_1 z w a b u)*(d1_11_2 z w a b u)))+((d0_3_0 z w a b u)*(d1_10_3 z w a b u)))))+((((d2_5_3 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_6_3 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_7_3 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_8_3 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_9_3 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_10_3 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_11_3 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_12_3 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_13_3 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_13_3 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_3,d1_11_2,d1_11_3,d1_12_2,d1_12_3,d1_13_2,d1_13_3,d2_10_3,d2_11_3,d2_12_3,d2_13_3,d2_5_3,d2_6_3,d2_7_3,d2_8_3,d2_9_3,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_13_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (z w a b u : ℂ) : (innerCertificate z w a b u)[4]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_13_4 z w a b u))+((d0_0_1 z w a b u)*(d1_13_3 z w a b u)))+((((d0_1_0 z w a b u)*(d1_12_4 z w a b u))+((d0_1_1 z w a b u)*(d1_12_3 z w a b u)))+((((d0_2_0 z w a b u)*(d1_11_4 z w a b u))+((d0_2_1 z w a b u)*(d1_11_3 z w a b u)))+((d0_3_0 z w a b u)*(d1_10_4 z w a b u)))))+((((d2_5_4 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_6_4 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_7_4 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_8_4 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_9_4 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_10_4 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_11_4 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_12_4 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_13_4 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_13_4 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_4,d1_11_3,d1_11_4,d1_12_3,d1_12_4,d1_13_3,d1_13_4,d2_10_4,d2_11_4,d2_12_4,d2_13_4,d2_5_4,d2_6_4,d2_7_4,d2_8_4,d2_9_4,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_13_4]
  ring
#print axioms coefficient_4

theorem coefficient_5 (z w a b u : ℂ) : (innerCertificate z w a b u)[5]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_13_5 z w a b u))+((d0_0_1 z w a b u)*(d1_13_4 z w a b u)))+((((d0_1_0 z w a b u)*(d1_12_5 z w a b u))+((d0_1_1 z w a b u)*(d1_12_4 z w a b u)))+((((d0_2_0 z w a b u)*(d1_11_5 z w a b u))+((d0_2_1 z w a b u)*(d1_11_4 z w a b u)))+((d0_3_0 z w a b u)*(d1_10_5 z w a b u)))))+((((d2_5_5 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_6_5 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_7_5 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_8_5 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_9_5 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_10_5 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_11_5 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_12_5 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_13_5 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_13_5 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_5,d1_11_4,d1_11_5,d1_12_4,d1_12_5,d1_13_4,d1_13_5,d2_10_5,d2_11_5,d2_12_5,d2_13_5,d2_5_5,d2_6_5,d2_7_5,d2_8_5,d2_9_5,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_13_5]
  ring
#print axioms coefficient_5

theorem coefficient_6 (z w a b u : ℂ) : (innerCertificate z w a b u)[6]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_13_6 z w a b u))+((d0_0_1 z w a b u)*(d1_13_5 z w a b u)))+((((d0_1_0 z w a b u)*(d1_12_6 z w a b u))+((d0_1_1 z w a b u)*(d1_12_5 z w a b u)))+((((d0_2_0 z w a b u)*(d1_11_6 z w a b u))+((d0_2_1 z w a b u)*(d1_11_5 z w a b u)))+((d0_3_0 z w a b u)*(d1_10_6 z w a b u)))))+((((d2_5_6 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_6_6 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_7_6 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_8_6 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_9_6 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_10_6 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_11_6 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_12_6 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_13_6 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_13_6 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_6,d1_11_5,d1_11_6,d1_12_5,d1_12_6,d1_13_5,d1_13_6,d2_10_6,d2_11_6,d2_12_6,d2_13_6,d2_5_6,d2_6_6,d2_7_6,d2_8_6,d2_9_6,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_13_6]
  ring
#print axioms coefficient_6

theorem coefficient_7 (z w a b u : ℂ) : (innerCertificate z w a b u)[7]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_13_7 z w a b u))+((d0_0_1 z w a b u)*(d1_13_6 z w a b u)))+((((d0_1_0 z w a b u)*(d1_12_7 z w a b u))+((d0_1_1 z w a b u)*(d1_12_6 z w a b u)))+((((d0_2_0 z w a b u)*(d1_11_7 z w a b u))+((d0_2_1 z w a b u)*(d1_11_6 z w a b u)))+((d0_3_0 z w a b u)*(d1_10_7 z w a b u)))))+((((d2_5_7 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_6_7 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_7_7 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_8_7 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_9_7 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_10_7 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_11_7 z w a b u)*(d3_2_0 z w a b u))+0)+(((d2_12_7 z w a b u)*(d3_1_0 z w a b u))+0)))))))))+((-1)*(d4_13_7 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_10_7,d1_11_6,d1_11_7,d1_12_6,d1_12_7,d1_13_6,d1_13_7,d2_10_7,d2_11_7,d2_12_7,d2_5_7,d2_6_7,d2_7_7,d2_8_7,d2_9_7,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_13_7]
  ring
#print axioms coefficient_7

theorem coefficient_8 (z w a b u : ℂ) : (innerCertificate z w a b u)[8]?=some 0 := by
  change some (((((d0_0_1 z w a b u)*(d1_13_7 z w a b u))+(((d0_1_1 z w a b u)*(d1_12_7 z w a b u))+((d0_2_1 z w a b u)*(d1_11_7 z w a b u))))+((-1)*(d4_13_8 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_1,d0_1_1,d0_2_1,d1_11_7,d1_12_7,d1_13_7,d4_13_8]
  ring
#print axioms coefficient_8

end SmallLevelTwentySixSource89Split13
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixSource89Split14
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89

theorem coefficient_0 (z w a b u : ℂ) : (innerCertificate z w a b u)[0]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_14_0 z w a b u))+0)+((((d0_1_0 z w a b u)*(d1_13_0 z w a b u))+0)+((((d0_2_0 z w a b u)*(d1_12_0 z w a b u))+0)+(((d0_3_0 z w a b u)*(d1_11_0 z w a b u))+0))))+((((d2_6_0 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_7_0 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_8_0 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_9_0 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_10_0 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_11_0 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_12_0 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_13_0 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_14_0 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+(((-1)*(d4_14_0 z w a b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_1_0,d0_2_0,d0_3_0,d1_11_0,d1_12_0,d1_13_0,d1_14_0,d2_10_0,d2_11_0,d2_12_0,d2_13_0,d2_14_0,d2_6_0,d2_7_0,d2_8_0,d2_9_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_14_0]
  ring
#print axioms coefficient_0

theorem coefficient_1 (z w a b u : ℂ) : (innerCertificate z w a b u)[1]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_14_1 z w a b u))+(((d0_0_1 z w a b u)*(d1_14_0 z w a b u))+0))+((((d0_1_0 z w a b u)*(d1_13_1 z w a b u))+(((d0_1_1 z w a b u)*(d1_13_0 z w a b u))+0))+((((d0_2_0 z w a b u)*(d1_12_1 z w a b u))+(((d0_2_1 z w a b u)*(d1_12_0 z w a b u))+0))+((d0_3_0 z w a b u)*(d1_11_1 z w a b u)))))+((((d2_6_1 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_7_1 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_8_1 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_9_1 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_10_1 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_11_1 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_12_1 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_13_1 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_14_1 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_14_1 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_11_1,d1_12_0,d1_12_1,d1_13_0,d1_13_1,d1_14_0,d1_14_1,d2_10_1,d2_11_1,d2_12_1,d2_13_1,d2_14_1,d2_6_1,d2_7_1,d2_8_1,d2_9_1,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_14_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (z w a b u : ℂ) : (innerCertificate z w a b u)[2]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_14_2 z w a b u))+((d0_0_1 z w a b u)*(d1_14_1 z w a b u)))+((((d0_1_0 z w a b u)*(d1_13_2 z w a b u))+((d0_1_1 z w a b u)*(d1_13_1 z w a b u)))+((((d0_2_0 z w a b u)*(d1_12_2 z w a b u))+((d0_2_1 z w a b u)*(d1_12_1 z w a b u)))+((d0_3_0 z w a b u)*(d1_11_2 z w a b u)))))+((((d2_6_2 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_7_2 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_8_2 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_9_2 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_10_2 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_11_2 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_12_2 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_13_2 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_14_2 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_14_2 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_11_2,d1_12_1,d1_12_2,d1_13_1,d1_13_2,d1_14_1,d1_14_2,d2_10_2,d2_11_2,d2_12_2,d2_13_2,d2_14_2,d2_6_2,d2_7_2,d2_8_2,d2_9_2,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_14_2]
  ring
#print axioms coefficient_2

theorem coefficient_3 (z w a b u : ℂ) : (innerCertificate z w a b u)[3]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_14_3 z w a b u))+((d0_0_1 z w a b u)*(d1_14_2 z w a b u)))+((((d0_1_0 z w a b u)*(d1_13_3 z w a b u))+((d0_1_1 z w a b u)*(d1_13_2 z w a b u)))+((((d0_2_0 z w a b u)*(d1_12_3 z w a b u))+((d0_2_1 z w a b u)*(d1_12_2 z w a b u)))+((d0_3_0 z w a b u)*(d1_11_3 z w a b u)))))+((((d2_6_3 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_7_3 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_8_3 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_9_3 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_10_3 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_11_3 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_12_3 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_13_3 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_14_3 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_14_3 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_11_3,d1_12_2,d1_12_3,d1_13_2,d1_13_3,d1_14_2,d1_14_3,d2_10_3,d2_11_3,d2_12_3,d2_13_3,d2_14_3,d2_6_3,d2_7_3,d2_8_3,d2_9_3,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_14_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (z w a b u : ℂ) : (innerCertificate z w a b u)[4]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_14_4 z w a b u))+((d0_0_1 z w a b u)*(d1_14_3 z w a b u)))+((((d0_1_0 z w a b u)*(d1_13_4 z w a b u))+((d0_1_1 z w a b u)*(d1_13_3 z w a b u)))+((((d0_2_0 z w a b u)*(d1_12_4 z w a b u))+((d0_2_1 z w a b u)*(d1_12_3 z w a b u)))+((d0_3_0 z w a b u)*(d1_11_4 z w a b u)))))+((((d2_6_4 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_7_4 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_8_4 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_9_4 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_10_4 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_11_4 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_12_4 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_13_4 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_14_4 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_14_4 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_11_4,d1_12_3,d1_12_4,d1_13_3,d1_13_4,d1_14_3,d1_14_4,d2_10_4,d2_11_4,d2_12_4,d2_13_4,d2_14_4,d2_6_4,d2_7_4,d2_8_4,d2_9_4,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_14_4]
  ring
#print axioms coefficient_4

theorem coefficient_5 (z w a b u : ℂ) : (innerCertificate z w a b u)[5]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_14_5 z w a b u))+((d0_0_1 z w a b u)*(d1_14_4 z w a b u)))+((((d0_1_0 z w a b u)*(d1_13_5 z w a b u))+((d0_1_1 z w a b u)*(d1_13_4 z w a b u)))+((((d0_2_0 z w a b u)*(d1_12_5 z w a b u))+((d0_2_1 z w a b u)*(d1_12_4 z w a b u)))+((d0_3_0 z w a b u)*(d1_11_5 z w a b u)))))+((((d2_6_5 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_7_5 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_8_5 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_9_5 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_10_5 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_11_5 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_12_5 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_13_5 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_14_5 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_14_5 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_11_5,d1_12_4,d1_12_5,d1_13_4,d1_13_5,d1_14_4,d1_14_5,d2_10_5,d2_11_5,d2_12_5,d2_13_5,d2_14_5,d2_6_5,d2_7_5,d2_8_5,d2_9_5,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_14_5]
  ring
#print axioms coefficient_5

theorem coefficient_6 (z w a b u : ℂ) : (innerCertificate z w a b u)[6]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_14_6 z w a b u))+((d0_0_1 z w a b u)*(d1_14_5 z w a b u)))+((((d0_1_0 z w a b u)*(d1_13_6 z w a b u))+((d0_1_1 z w a b u)*(d1_13_5 z w a b u)))+((((d0_2_0 z w a b u)*(d1_12_6 z w a b u))+((d0_2_1 z w a b u)*(d1_12_5 z w a b u)))+((d0_3_0 z w a b u)*(d1_11_6 z w a b u)))))+((((d2_6_6 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_7_6 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_8_6 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_9_6 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_10_6 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_11_6 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_12_6 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_13_6 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_14_6 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_14_6 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_11_6,d1_12_5,d1_12_6,d1_13_5,d1_13_6,d1_14_5,d1_14_6,d2_10_6,d2_11_6,d2_12_6,d2_13_6,d2_14_6,d2_6_6,d2_7_6,d2_8_6,d2_9_6,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_14_6]
  ring
#print axioms coefficient_6

theorem coefficient_7 (z w a b u : ℂ) : (innerCertificate z w a b u)[7]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_14_7 z w a b u))+((d0_0_1 z w a b u)*(d1_14_6 z w a b u)))+((((d0_1_0 z w a b u)*(d1_13_7 z w a b u))+((d0_1_1 z w a b u)*(d1_13_6 z w a b u)))+((((d0_2_0 z w a b u)*(d1_12_7 z w a b u))+((d0_2_1 z w a b u)*(d1_12_6 z w a b u)))+((d0_3_0 z w a b u)*(d1_11_7 z w a b u)))))+((((d2_6_7 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_7_7 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_8_7 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_9_7 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_10_7 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_11_7 z w a b u)*(d3_3_0 z w a b u))+0)+(((d2_12_7 z w a b u)*(d3_2_0 z w a b u))+0))))))))+((-1)*(d4_14_7 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_11_7,d1_12_6,d1_12_7,d1_13_6,d1_13_7,d1_14_6,d1_14_7,d2_10_7,d2_11_7,d2_12_7,d2_6_7,d2_7_7,d2_8_7,d2_9_7,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_14_7]
  ring
#print axioms coefficient_7

theorem coefficient_8 (z w a b u : ℂ) : (innerCertificate z w a b u)[8]?=some 0 := by
  change some (((((d0_0_1 z w a b u)*(d1_14_7 z w a b u))+(((d0_1_1 z w a b u)*(d1_13_7 z w a b u))+((d0_2_1 z w a b u)*(d1_12_7 z w a b u))))+((-1)*(d4_14_8 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_1,d0_1_1,d0_2_1,d1_12_7,d1_13_7,d1_14_7,d4_14_8]
  ring
#print axioms coefficient_8

end SmallLevelTwentySixSource89Split14
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixSource89Split15
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89

theorem coefficient_0 (z w a b u : ℂ) : (innerCertificate z w a b u)[0]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_15_0 z w a b u))+0)+((((d0_1_0 z w a b u)*(d1_14_0 z w a b u))+0)+((((d0_2_0 z w a b u)*(d1_13_0 z w a b u))+0)+(((d0_3_0 z w a b u)*(d1_12_0 z w a b u))+0))))+((((d2_7_0 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_8_0 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_9_0 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_10_0 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_11_0 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_12_0 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_13_0 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_14_0 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_15_0 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+(((-1)*(d4_15_0 z w a b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_1_0,d0_2_0,d0_3_0,d1_12_0,d1_13_0,d1_14_0,d1_15_0,d2_10_0,d2_11_0,d2_12_0,d2_13_0,d2_14_0,d2_15_0,d2_7_0,d2_8_0,d2_9_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_15_0]
  ring
#print axioms coefficient_0

theorem coefficient_1 (z w a b u : ℂ) : (innerCertificate z w a b u)[1]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_15_1 z w a b u))+(((d0_0_1 z w a b u)*(d1_15_0 z w a b u))+0))+((((d0_1_0 z w a b u)*(d1_14_1 z w a b u))+(((d0_1_1 z w a b u)*(d1_14_0 z w a b u))+0))+((((d0_2_0 z w a b u)*(d1_13_1 z w a b u))+(((d0_2_1 z w a b u)*(d1_13_0 z w a b u))+0))+((d0_3_0 z w a b u)*(d1_12_1 z w a b u)))))+((((d2_7_1 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_8_1 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_9_1 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_10_1 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_11_1 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_12_1 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_13_1 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_14_1 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_15_1 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_15_1 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_12_1,d1_13_0,d1_13_1,d1_14_0,d1_14_1,d1_15_0,d1_15_1,d2_10_1,d2_11_1,d2_12_1,d2_13_1,d2_14_1,d2_15_1,d2_7_1,d2_8_1,d2_9_1,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_15_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (z w a b u : ℂ) : (innerCertificate z w a b u)[2]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_15_2 z w a b u))+((d0_0_1 z w a b u)*(d1_15_1 z w a b u)))+((((d0_1_0 z w a b u)*(d1_14_2 z w a b u))+((d0_1_1 z w a b u)*(d1_14_1 z w a b u)))+((((d0_2_0 z w a b u)*(d1_13_2 z w a b u))+((d0_2_1 z w a b u)*(d1_13_1 z w a b u)))+((d0_3_0 z w a b u)*(d1_12_2 z w a b u)))))+((((d2_7_2 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_8_2 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_9_2 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_10_2 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_11_2 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_12_2 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_13_2 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_14_2 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_15_2 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_15_2 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_12_2,d1_13_1,d1_13_2,d1_14_1,d1_14_2,d1_15_1,d1_15_2,d2_10_2,d2_11_2,d2_12_2,d2_13_2,d2_14_2,d2_15_2,d2_7_2,d2_8_2,d2_9_2,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_15_2]
  ring
#print axioms coefficient_2

theorem coefficient_3 (z w a b u : ℂ) : (innerCertificate z w a b u)[3]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_15_3 z w a b u))+((d0_0_1 z w a b u)*(d1_15_2 z w a b u)))+((((d0_1_0 z w a b u)*(d1_14_3 z w a b u))+((d0_1_1 z w a b u)*(d1_14_2 z w a b u)))+((((d0_2_0 z w a b u)*(d1_13_3 z w a b u))+((d0_2_1 z w a b u)*(d1_13_2 z w a b u)))+((d0_3_0 z w a b u)*(d1_12_3 z w a b u)))))+((((d2_7_3 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_8_3 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_9_3 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_10_3 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_11_3 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_12_3 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_13_3 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_14_3 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_15_3 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_15_3 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_12_3,d1_13_2,d1_13_3,d1_14_2,d1_14_3,d1_15_2,d1_15_3,d2_10_3,d2_11_3,d2_12_3,d2_13_3,d2_14_3,d2_15_3,d2_7_3,d2_8_3,d2_9_3,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_15_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (z w a b u : ℂ) : (innerCertificate z w a b u)[4]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_15_4 z w a b u))+((d0_0_1 z w a b u)*(d1_15_3 z w a b u)))+((((d0_1_0 z w a b u)*(d1_14_4 z w a b u))+((d0_1_1 z w a b u)*(d1_14_3 z w a b u)))+((((d0_2_0 z w a b u)*(d1_13_4 z w a b u))+((d0_2_1 z w a b u)*(d1_13_3 z w a b u)))+((d0_3_0 z w a b u)*(d1_12_4 z w a b u)))))+((((d2_7_4 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_8_4 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_9_4 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_10_4 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_11_4 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_12_4 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_13_4 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_14_4 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_15_4 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_15_4 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_12_4,d1_13_3,d1_13_4,d1_14_3,d1_14_4,d1_15_3,d1_15_4,d2_10_4,d2_11_4,d2_12_4,d2_13_4,d2_14_4,d2_15_4,d2_7_4,d2_8_4,d2_9_4,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_15_4]
  ring
#print axioms coefficient_4

theorem coefficient_5 (z w a b u : ℂ) : (innerCertificate z w a b u)[5]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_15_5 z w a b u))+((d0_0_1 z w a b u)*(d1_15_4 z w a b u)))+((((d0_1_0 z w a b u)*(d1_14_5 z w a b u))+((d0_1_1 z w a b u)*(d1_14_4 z w a b u)))+((((d0_2_0 z w a b u)*(d1_13_5 z w a b u))+((d0_2_1 z w a b u)*(d1_13_4 z w a b u)))+((d0_3_0 z w a b u)*(d1_12_5 z w a b u)))))+((((d2_7_5 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_8_5 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_9_5 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_10_5 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_11_5 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_12_5 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_13_5 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_14_5 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_15_5 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_15_5 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_12_5,d1_13_4,d1_13_5,d1_14_4,d1_14_5,d1_15_4,d1_15_5,d2_10_5,d2_11_5,d2_12_5,d2_13_5,d2_14_5,d2_15_5,d2_7_5,d2_8_5,d2_9_5,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_15_5]
  ring
#print axioms coefficient_5

theorem coefficient_6 (z w a b u : ℂ) : (innerCertificate z w a b u)[6]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_15_6 z w a b u))+((d0_0_1 z w a b u)*(d1_15_5 z w a b u)))+((((d0_1_0 z w a b u)*(d1_14_6 z w a b u))+((d0_1_1 z w a b u)*(d1_14_5 z w a b u)))+((((d0_2_0 z w a b u)*(d1_13_6 z w a b u))+((d0_2_1 z w a b u)*(d1_13_5 z w a b u)))+((d0_3_0 z w a b u)*(d1_12_6 z w a b u)))))+((((d2_7_6 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_8_6 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_9_6 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_10_6 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_11_6 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_12_6 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_13_6 z w a b u)*(d3_2_0 z w a b u))+0)+(((d2_14_6 z w a b u)*(d3_1_0 z w a b u))+0)))))))))+((-1)*(d4_15_6 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_12_6,d1_13_5,d1_13_6,d1_14_5,d1_14_6,d1_15_5,d1_15_6,d2_10_6,d2_11_6,d2_12_6,d2_13_6,d2_14_6,d2_7_6,d2_8_6,d2_9_6,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_15_6]
  ring
#print axioms coefficient_6

theorem coefficient_7 (z w a b u : ℂ) : (innerCertificate z w a b u)[7]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_15_7 z w a b u))+((d0_0_1 z w a b u)*(d1_15_6 z w a b u)))+((((d0_1_0 z w a b u)*(d1_14_7 z w a b u))+((d0_1_1 z w a b u)*(d1_14_6 z w a b u)))+((((d0_2_0 z w a b u)*(d1_13_7 z w a b u))+((d0_2_1 z w a b u)*(d1_13_6 z w a b u)))+((d0_3_0 z w a b u)*(d1_12_7 z w a b u)))))+((((d2_7_7 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_8_7 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_9_7 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_10_7 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_11_7 z w a b u)*(d3_4_0 z w a b u))+0)+(((d2_12_7 z w a b u)*(d3_3_0 z w a b u))+0)))))))+((-1)*(d4_15_7 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_12_7,d1_13_6,d1_13_7,d1_14_6,d1_14_7,d1_15_6,d1_15_7,d2_10_7,d2_11_7,d2_12_7,d2_7_7,d2_8_7,d2_9_7,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_15_7]
  ring
#print axioms coefficient_7

theorem coefficient_8 (z w a b u : ℂ) : (innerCertificate z w a b u)[8]?=some 0 := by
  change some (((((d0_0_1 z w a b u)*(d1_15_7 z w a b u))+(((d0_1_1 z w a b u)*(d1_14_7 z w a b u))+((d0_2_1 z w a b u)*(d1_13_7 z w a b u))))+((-1)*(d4_15_8 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_1,d0_1_1,d0_2_1,d1_13_7,d1_14_7,d1_15_7,d4_15_8]
  ring
#print axioms coefficient_8

end SmallLevelTwentySixSource89Split15
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixSource89Split16
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89

theorem coefficient_0 (z w a b u : ℂ) : (innerCertificate z w a b u)[0]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_16_0 z w a b u))+0)+((((d0_1_0 z w a b u)*(d1_15_0 z w a b u))+0)+((((d0_2_0 z w a b u)*(d1_14_0 z w a b u))+0)+(((d0_3_0 z w a b u)*(d1_13_0 z w a b u))+0))))+((((d2_8_0 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_9_0 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_10_0 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_11_0 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_12_0 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_13_0 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_14_0 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_15_0 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_16_0 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+(((-1)*(d4_16_0 z w a b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_1_0,d0_2_0,d0_3_0,d1_13_0,d1_14_0,d1_15_0,d1_16_0,d2_10_0,d2_11_0,d2_12_0,d2_13_0,d2_14_0,d2_15_0,d2_16_0,d2_8_0,d2_9_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_16_0]
  ring
#print axioms coefficient_0

theorem coefficient_1 (z w a b u : ℂ) : (innerCertificate z w a b u)[1]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_16_1 z w a b u))+(((d0_0_1 z w a b u)*(d1_16_0 z w a b u))+0))+((((d0_1_0 z w a b u)*(d1_15_1 z w a b u))+(((d0_1_1 z w a b u)*(d1_15_0 z w a b u))+0))+((((d0_2_0 z w a b u)*(d1_14_1 z w a b u))+(((d0_2_1 z w a b u)*(d1_14_0 z w a b u))+0))+((d0_3_0 z w a b u)*(d1_13_1 z w a b u)))))+((((d2_8_1 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_9_1 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_10_1 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_11_1 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_12_1 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_13_1 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_14_1 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_15_1 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_16_1 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_16_1 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_13_1,d1_14_0,d1_14_1,d1_15_0,d1_15_1,d1_16_0,d1_16_1,d2_10_1,d2_11_1,d2_12_1,d2_13_1,d2_14_1,d2_15_1,d2_16_1,d2_8_1,d2_9_1,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_16_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (z w a b u : ℂ) : (innerCertificate z w a b u)[2]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_16_2 z w a b u))+((d0_0_1 z w a b u)*(d1_16_1 z w a b u)))+((((d0_1_0 z w a b u)*(d1_15_2 z w a b u))+((d0_1_1 z w a b u)*(d1_15_1 z w a b u)))+((((d0_2_0 z w a b u)*(d1_14_2 z w a b u))+((d0_2_1 z w a b u)*(d1_14_1 z w a b u)))+((d0_3_0 z w a b u)*(d1_13_2 z w a b u)))))+((((d2_8_2 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_9_2 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_10_2 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_11_2 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_12_2 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_13_2 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_14_2 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_15_2 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_16_2 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_16_2 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_13_2,d1_14_1,d1_14_2,d1_15_1,d1_15_2,d1_16_1,d1_16_2,d2_10_2,d2_11_2,d2_12_2,d2_13_2,d2_14_2,d2_15_2,d2_16_2,d2_8_2,d2_9_2,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_16_2]
  ring
#print axioms coefficient_2

theorem coefficient_3 (z w a b u : ℂ) : (innerCertificate z w a b u)[3]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_16_3 z w a b u))+((d0_0_1 z w a b u)*(d1_16_2 z w a b u)))+((((d0_1_0 z w a b u)*(d1_15_3 z w a b u))+((d0_1_1 z w a b u)*(d1_15_2 z w a b u)))+((((d0_2_0 z w a b u)*(d1_14_3 z w a b u))+((d0_2_1 z w a b u)*(d1_14_2 z w a b u)))+((d0_3_0 z w a b u)*(d1_13_3 z w a b u)))))+((((d2_8_3 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_9_3 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_10_3 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_11_3 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_12_3 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_13_3 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_14_3 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_15_3 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_16_3 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_16_3 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_13_3,d1_14_2,d1_14_3,d1_15_2,d1_15_3,d1_16_2,d1_16_3,d2_10_3,d2_11_3,d2_12_3,d2_13_3,d2_14_3,d2_15_3,d2_16_3,d2_8_3,d2_9_3,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_16_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (z w a b u : ℂ) : (innerCertificate z w a b u)[4]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_16_4 z w a b u))+((d0_0_1 z w a b u)*(d1_16_3 z w a b u)))+((((d0_1_0 z w a b u)*(d1_15_4 z w a b u))+((d0_1_1 z w a b u)*(d1_15_3 z w a b u)))+((((d0_2_0 z w a b u)*(d1_14_4 z w a b u))+((d0_2_1 z w a b u)*(d1_14_3 z w a b u)))+((d0_3_0 z w a b u)*(d1_13_4 z w a b u)))))+((((d2_8_4 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_9_4 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_10_4 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_11_4 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_12_4 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_13_4 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_14_4 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_15_4 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_16_4 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_16_4 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_13_4,d1_14_3,d1_14_4,d1_15_3,d1_15_4,d1_16_3,d1_16_4,d2_10_4,d2_11_4,d2_12_4,d2_13_4,d2_14_4,d2_15_4,d2_16_4,d2_8_4,d2_9_4,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_16_4]
  ring
#print axioms coefficient_4

theorem coefficient_5 (z w a b u : ℂ) : (innerCertificate z w a b u)[5]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_16_5 z w a b u))+((d0_0_1 z w a b u)*(d1_16_4 z w a b u)))+((((d0_1_0 z w a b u)*(d1_15_5 z w a b u))+((d0_1_1 z w a b u)*(d1_15_4 z w a b u)))+((((d0_2_0 z w a b u)*(d1_14_5 z w a b u))+((d0_2_1 z w a b u)*(d1_14_4 z w a b u)))+((d0_3_0 z w a b u)*(d1_13_5 z w a b u)))))+((((d2_8_5 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_9_5 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_10_5 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_11_5 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_12_5 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_13_5 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_14_5 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_15_5 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_16_5 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_16_5 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_13_5,d1_14_4,d1_14_5,d1_15_4,d1_15_5,d1_16_4,d1_16_5,d2_10_5,d2_11_5,d2_12_5,d2_13_5,d2_14_5,d2_15_5,d2_16_5,d2_8_5,d2_9_5,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_16_5]
  ring
#print axioms coefficient_5

theorem coefficient_6 (z w a b u : ℂ) : (innerCertificate z w a b u)[6]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_16_6 z w a b u))+((d0_0_1 z w a b u)*(d1_16_5 z w a b u)))+((((d0_1_0 z w a b u)*(d1_15_6 z w a b u))+((d0_1_1 z w a b u)*(d1_15_5 z w a b u)))+((((d0_2_0 z w a b u)*(d1_14_6 z w a b u))+((d0_2_1 z w a b u)*(d1_14_5 z w a b u)))+((d0_3_0 z w a b u)*(d1_13_6 z w a b u)))))+((((d2_8_6 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_9_6 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_10_6 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_11_6 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_12_6 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_13_6 z w a b u)*(d3_3_0 z w a b u))+0)+(((d2_14_6 z w a b u)*(d3_2_0 z w a b u))+0))))))))+((-1)*(d4_16_6 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_13_6,d1_14_5,d1_14_6,d1_15_5,d1_15_6,d1_16_5,d1_16_6,d2_10_6,d2_11_6,d2_12_6,d2_13_6,d2_14_6,d2_8_6,d2_9_6,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_16_6]
  ring
#print axioms coefficient_6

theorem coefficient_7 (z w a b u : ℂ) : (innerCertificate z w a b u)[7]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_16_7 z w a b u))+((d0_0_1 z w a b u)*(d1_16_6 z w a b u)))+((((d0_1_0 z w a b u)*(d1_15_7 z w a b u))+((d0_1_1 z w a b u)*(d1_15_6 z w a b u)))+((((d0_2_0 z w a b u)*(d1_14_7 z w a b u))+((d0_2_1 z w a b u)*(d1_14_6 z w a b u)))+((d0_3_0 z w a b u)*(d1_13_7 z w a b u)))))+((((d2_8_7 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_9_7 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_10_7 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_11_7 z w a b u)*(d3_5_0 z w a b u))+0)+(((d2_12_7 z w a b u)*(d3_4_0 z w a b u))+0))))))+((-1)*(d4_16_7 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_13_7,d1_14_6,d1_14_7,d1_15_6,d1_15_7,d1_16_6,d1_16_7,d2_10_7,d2_11_7,d2_12_7,d2_8_7,d2_9_7,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_16_7]
  ring
#print axioms coefficient_7

theorem coefficient_8 (z w a b u : ℂ) : (innerCertificate z w a b u)[8]?=some 0 := by
  change some (((((d0_0_1 z w a b u)*(d1_16_7 z w a b u))+(((d0_1_1 z w a b u)*(d1_15_7 z w a b u))+((d0_2_1 z w a b u)*(d1_14_7 z w a b u))))+((-1)*(d4_16_8 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_1,d0_1_1,d0_2_1,d1_14_7,d1_15_7,d1_16_7,d4_16_8]
  ring
#print axioms coefficient_8

end SmallLevelTwentySixSource89Split16
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixSource89Split17
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89

theorem coefficient_0 (z w a b u : ℂ) : (innerCertificate z w a b u)[0]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_17_0 z w a b u))+0)+((((d0_1_0 z w a b u)*(d1_16_0 z w a b u))+0)+((((d0_2_0 z w a b u)*(d1_15_0 z w a b u))+0)+(((d0_3_0 z w a b u)*(d1_14_0 z w a b u))+0))))+((((d2_9_0 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_10_0 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_11_0 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_12_0 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_13_0 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_14_0 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_15_0 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_16_0 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_17_0 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+(((-1)*(d4_17_0 z w a b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_1_0,d0_2_0,d0_3_0,d1_14_0,d1_15_0,d1_16_0,d1_17_0,d2_10_0,d2_11_0,d2_12_0,d2_13_0,d2_14_0,d2_15_0,d2_16_0,d2_17_0,d2_9_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_17_0]
  ring
#print axioms coefficient_0

theorem coefficient_1 (z w a b u : ℂ) : (innerCertificate z w a b u)[1]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_17_1 z w a b u))+(((d0_0_1 z w a b u)*(d1_17_0 z w a b u))+0))+((((d0_1_0 z w a b u)*(d1_16_1 z w a b u))+(((d0_1_1 z w a b u)*(d1_16_0 z w a b u))+0))+((((d0_2_0 z w a b u)*(d1_15_1 z w a b u))+(((d0_2_1 z w a b u)*(d1_15_0 z w a b u))+0))+((d0_3_0 z w a b u)*(d1_14_1 z w a b u)))))+((((d2_9_1 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_10_1 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_11_1 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_12_1 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_13_1 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_14_1 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_15_1 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_16_1 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_17_1 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_17_1 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_14_1,d1_15_0,d1_15_1,d1_16_0,d1_16_1,d1_17_0,d1_17_1,d2_10_1,d2_11_1,d2_12_1,d2_13_1,d2_14_1,d2_15_1,d2_16_1,d2_17_1,d2_9_1,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_17_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (z w a b u : ℂ) : (innerCertificate z w a b u)[2]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_17_2 z w a b u))+((d0_0_1 z w a b u)*(d1_17_1 z w a b u)))+((((d0_1_0 z w a b u)*(d1_16_2 z w a b u))+((d0_1_1 z w a b u)*(d1_16_1 z w a b u)))+((((d0_2_0 z w a b u)*(d1_15_2 z w a b u))+((d0_2_1 z w a b u)*(d1_15_1 z w a b u)))+((d0_3_0 z w a b u)*(d1_14_2 z w a b u)))))+((((d2_9_2 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_10_2 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_11_2 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_12_2 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_13_2 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_14_2 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_15_2 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_16_2 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_17_2 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_17_2 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_14_2,d1_15_1,d1_15_2,d1_16_1,d1_16_2,d1_17_1,d1_17_2,d2_10_2,d2_11_2,d2_12_2,d2_13_2,d2_14_2,d2_15_2,d2_16_2,d2_17_2,d2_9_2,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_17_2]
  ring
#print axioms coefficient_2

theorem coefficient_3 (z w a b u : ℂ) : (innerCertificate z w a b u)[3]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_17_3 z w a b u))+((d0_0_1 z w a b u)*(d1_17_2 z w a b u)))+((((d0_1_0 z w a b u)*(d1_16_3 z w a b u))+((d0_1_1 z w a b u)*(d1_16_2 z w a b u)))+((((d0_2_0 z w a b u)*(d1_15_3 z w a b u))+((d0_2_1 z w a b u)*(d1_15_2 z w a b u)))+((d0_3_0 z w a b u)*(d1_14_3 z w a b u)))))+((((d2_9_3 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_10_3 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_11_3 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_12_3 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_13_3 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_14_3 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_15_3 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_16_3 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_17_3 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_17_3 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_14_3,d1_15_2,d1_15_3,d1_16_2,d1_16_3,d1_17_2,d1_17_3,d2_10_3,d2_11_3,d2_12_3,d2_13_3,d2_14_3,d2_15_3,d2_16_3,d2_17_3,d2_9_3,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_17_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (z w a b u : ℂ) : (innerCertificate z w a b u)[4]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_17_4 z w a b u))+((d0_0_1 z w a b u)*(d1_17_3 z w a b u)))+((((d0_1_0 z w a b u)*(d1_16_4 z w a b u))+((d0_1_1 z w a b u)*(d1_16_3 z w a b u)))+((((d0_2_0 z w a b u)*(d1_15_4 z w a b u))+((d0_2_1 z w a b u)*(d1_15_3 z w a b u)))+((d0_3_0 z w a b u)*(d1_14_4 z w a b u)))))+((((d2_9_4 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_10_4 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_11_4 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_12_4 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_13_4 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_14_4 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_15_4 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_16_4 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_17_4 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_17_4 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_14_4,d1_15_3,d1_15_4,d1_16_3,d1_16_4,d1_17_3,d1_17_4,d2_10_4,d2_11_4,d2_12_4,d2_13_4,d2_14_4,d2_15_4,d2_16_4,d2_17_4,d2_9_4,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_17_4]
  ring
#print axioms coefficient_4

theorem coefficient_5 (z w a b u : ℂ) : (innerCertificate z w a b u)[5]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_17_5 z w a b u))+((d0_0_1 z w a b u)*(d1_17_4 z w a b u)))+((((d0_1_0 z w a b u)*(d1_16_5 z w a b u))+((d0_1_1 z w a b u)*(d1_16_4 z w a b u)))+((((d0_2_0 z w a b u)*(d1_15_5 z w a b u))+((d0_2_1 z w a b u)*(d1_15_4 z w a b u)))+((d0_3_0 z w a b u)*(d1_14_5 z w a b u)))))+((((d2_9_5 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_10_5 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_11_5 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_12_5 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_13_5 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_14_5 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_15_5 z w a b u)*(d3_2_0 z w a b u))+0)+(((d2_16_5 z w a b u)*(d3_1_0 z w a b u))+0)))))))))+((-1)*(d4_17_5 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_14_5,d1_15_4,d1_15_5,d1_16_4,d1_16_5,d1_17_4,d1_17_5,d2_10_5,d2_11_5,d2_12_5,d2_13_5,d2_14_5,d2_15_5,d2_16_5,d2_9_5,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_17_5]
  ring
#print axioms coefficient_5

theorem coefficient_6 (z w a b u : ℂ) : (innerCertificate z w a b u)[6]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_17_6 z w a b u))+((d0_0_1 z w a b u)*(d1_17_5 z w a b u)))+((((d0_1_0 z w a b u)*(d1_16_6 z w a b u))+((d0_1_1 z w a b u)*(d1_16_5 z w a b u)))+((((d0_2_0 z w a b u)*(d1_15_6 z w a b u))+((d0_2_1 z w a b u)*(d1_15_5 z w a b u)))+((d0_3_0 z w a b u)*(d1_14_6 z w a b u)))))+((((d2_9_6 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_10_6 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_11_6 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_12_6 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_13_6 z w a b u)*(d3_4_0 z w a b u))+0)+(((d2_14_6 z w a b u)*(d3_3_0 z w a b u))+0)))))))+((-1)*(d4_17_6 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_14_6,d1_15_5,d1_15_6,d1_16_5,d1_16_6,d1_17_5,d1_17_6,d2_10_6,d2_11_6,d2_12_6,d2_13_6,d2_14_6,d2_9_6,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_17_6]
  ring
#print axioms coefficient_6

theorem coefficient_7 (z w a b u : ℂ) : (innerCertificate z w a b u)[7]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_17_7 z w a b u))+((d0_0_1 z w a b u)*(d1_17_6 z w a b u)))+((((d0_1_0 z w a b u)*(d1_16_7 z w a b u))+((d0_1_1 z w a b u)*(d1_16_6 z w a b u)))+((((d0_2_0 z w a b u)*(d1_15_7 z w a b u))+((d0_2_1 z w a b u)*(d1_15_6 z w a b u)))+((d0_3_0 z w a b u)*(d1_14_7 z w a b u)))))+((((d2_9_7 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_10_7 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_11_7 z w a b u)*(d3_6_0 z w a b u))+0)+(((d2_12_7 z w a b u)*(d3_5_0 z w a b u))+0)))))+((-1)*(d4_17_7 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_14_7,d1_15_6,d1_15_7,d1_16_6,d1_16_7,d1_17_6,d1_17_7,d2_10_7,d2_11_7,d2_12_7,d2_9_7,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_17_7]
  ring
#print axioms coefficient_7

theorem coefficient_8 (z w a b u : ℂ) : (innerCertificate z w a b u)[8]?=some 0 := by
  change some (((((d0_0_1 z w a b u)*(d1_17_7 z w a b u))+(((d0_1_1 z w a b u)*(d1_16_7 z w a b u))+((d0_2_1 z w a b u)*(d1_15_7 z w a b u))))+((-1)*(d4_17_8 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_1,d0_1_1,d0_2_1,d1_15_7,d1_16_7,d1_17_7,d4_17_8]
  ring
#print axioms coefficient_8

end SmallLevelTwentySixSource89Split17
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixSource89Split18
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89

theorem coefficient_0 (z w a b u : ℂ) : (innerCertificate z w a b u)[0]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_18_0 z w a b u))+0)+((((d0_1_0 z w a b u)*(d1_17_0 z w a b u))+0)+((((d0_2_0 z w a b u)*(d1_16_0 z w a b u))+0)+(((d0_3_0 z w a b u)*(d1_15_0 z w a b u))+0))))+((((d2_10_0 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_11_0 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_12_0 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_13_0 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_14_0 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_15_0 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_16_0 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_17_0 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_18_0 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+(((-1)*(d4_18_0 z w a b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_1_0,d0_2_0,d0_3_0,d1_15_0,d1_16_0,d1_17_0,d1_18_0,d2_10_0,d2_11_0,d2_12_0,d2_13_0,d2_14_0,d2_15_0,d2_16_0,d2_17_0,d2_18_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_18_0]
  ring
#print axioms coefficient_0

theorem coefficient_1 (z w a b u : ℂ) : (innerCertificate z w a b u)[1]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_18_1 z w a b u))+(((d0_0_1 z w a b u)*(d1_18_0 z w a b u))+0))+((((d0_1_0 z w a b u)*(d1_17_1 z w a b u))+(((d0_1_1 z w a b u)*(d1_17_0 z w a b u))+0))+((((d0_2_0 z w a b u)*(d1_16_1 z w a b u))+(((d0_2_1 z w a b u)*(d1_16_0 z w a b u))+0))+((d0_3_0 z w a b u)*(d1_15_1 z w a b u)))))+((((d2_10_1 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_11_1 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_12_1 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_13_1 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_14_1 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_15_1 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_16_1 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_17_1 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_18_1 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_18_1 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_15_1,d1_16_0,d1_16_1,d1_17_0,d1_17_1,d1_18_0,d1_18_1,d2_10_1,d2_11_1,d2_12_1,d2_13_1,d2_14_1,d2_15_1,d2_16_1,d2_17_1,d2_18_1,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_18_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (z w a b u : ℂ) : (innerCertificate z w a b u)[2]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_18_2 z w a b u))+((d0_0_1 z w a b u)*(d1_18_1 z w a b u)))+((((d0_1_0 z w a b u)*(d1_17_2 z w a b u))+((d0_1_1 z w a b u)*(d1_17_1 z w a b u)))+((((d0_2_0 z w a b u)*(d1_16_2 z w a b u))+((d0_2_1 z w a b u)*(d1_16_1 z w a b u)))+((d0_3_0 z w a b u)*(d1_15_2 z w a b u)))))+((((d2_10_2 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_11_2 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_12_2 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_13_2 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_14_2 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_15_2 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_16_2 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_17_2 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_18_2 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_18_2 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_15_2,d1_16_1,d1_16_2,d1_17_1,d1_17_2,d1_18_1,d1_18_2,d2_10_2,d2_11_2,d2_12_2,d2_13_2,d2_14_2,d2_15_2,d2_16_2,d2_17_2,d2_18_2,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_18_2]
  ring
#print axioms coefficient_2

theorem coefficient_3 (z w a b u : ℂ) : (innerCertificate z w a b u)[3]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_18_3 z w a b u))+((d0_0_1 z w a b u)*(d1_18_2 z w a b u)))+((((d0_1_0 z w a b u)*(d1_17_3 z w a b u))+((d0_1_1 z w a b u)*(d1_17_2 z w a b u)))+((((d0_2_0 z w a b u)*(d1_16_3 z w a b u))+((d0_2_1 z w a b u)*(d1_16_2 z w a b u)))+((d0_3_0 z w a b u)*(d1_15_3 z w a b u)))))+((((d2_10_3 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_11_3 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_12_3 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_13_3 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_14_3 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_15_3 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_16_3 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_17_3 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_18_3 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_18_3 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_15_3,d1_16_2,d1_16_3,d1_17_2,d1_17_3,d1_18_2,d1_18_3,d2_10_3,d2_11_3,d2_12_3,d2_13_3,d2_14_3,d2_15_3,d2_16_3,d2_17_3,d2_18_3,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_18_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (z w a b u : ℂ) : (innerCertificate z w a b u)[4]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_18_4 z w a b u))+((d0_0_1 z w a b u)*(d1_18_3 z w a b u)))+((((d0_1_0 z w a b u)*(d1_17_4 z w a b u))+((d0_1_1 z w a b u)*(d1_17_3 z w a b u)))+((((d0_2_0 z w a b u)*(d1_16_4 z w a b u))+((d0_2_1 z w a b u)*(d1_16_3 z w a b u)))+((d0_3_0 z w a b u)*(d1_15_4 z w a b u)))))+((((d2_10_4 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_11_4 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_12_4 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_13_4 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_14_4 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_15_4 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_16_4 z w a b u)*(d3_2_0 z w a b u))+0)+(((d2_17_4 z w a b u)*(d3_1_0 z w a b u))+0)))))))))+((-1)*(d4_18_4 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_15_4,d1_16_3,d1_16_4,d1_17_3,d1_17_4,d1_18_3,d1_18_4,d2_10_4,d2_11_4,d2_12_4,d2_13_4,d2_14_4,d2_15_4,d2_16_4,d2_17_4,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_18_4]
  ring
#print axioms coefficient_4

theorem coefficient_5 (z w a b u : ℂ) : (innerCertificate z w a b u)[5]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_18_5 z w a b u))+((d0_0_1 z w a b u)*(d1_18_4 z w a b u)))+((((d0_1_0 z w a b u)*(d1_17_5 z w a b u))+((d0_1_1 z w a b u)*(d1_17_4 z w a b u)))+((((d0_2_0 z w a b u)*(d1_16_5 z w a b u))+((d0_2_1 z w a b u)*(d1_16_4 z w a b u)))+((d0_3_0 z w a b u)*(d1_15_5 z w a b u)))))+((((d2_10_5 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_11_5 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_12_5 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_13_5 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_14_5 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_15_5 z w a b u)*(d3_3_0 z w a b u))+0)+(((d2_16_5 z w a b u)*(d3_2_0 z w a b u))+0))))))))+((-1)*(d4_18_5 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_15_5,d1_16_4,d1_16_5,d1_17_4,d1_17_5,d1_18_4,d1_18_5,d2_10_5,d2_11_5,d2_12_5,d2_13_5,d2_14_5,d2_15_5,d2_16_5,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_18_5]
  ring
#print axioms coefficient_5

theorem coefficient_6 (z w a b u : ℂ) : (innerCertificate z w a b u)[6]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_18_6 z w a b u))+((d0_0_1 z w a b u)*(d1_18_5 z w a b u)))+((((d0_1_0 z w a b u)*(d1_17_6 z w a b u))+((d0_1_1 z w a b u)*(d1_17_5 z w a b u)))+((((d0_2_0 z w a b u)*(d1_16_6 z w a b u))+((d0_2_1 z w a b u)*(d1_16_5 z w a b u)))+((d0_3_0 z w a b u)*(d1_15_6 z w a b u)))))+((((d2_10_6 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_11_6 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_12_6 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_13_6 z w a b u)*(d3_5_0 z w a b u))+0)+(((d2_14_6 z w a b u)*(d3_4_0 z w a b u))+0))))))+((-1)*(d4_18_6 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_15_6,d1_16_5,d1_16_6,d1_17_5,d1_17_6,d1_18_5,d1_18_6,d2_10_6,d2_11_6,d2_12_6,d2_13_6,d2_14_6,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_18_6]
  ring
#print axioms coefficient_6

theorem coefficient_7 (z w a b u : ℂ) : (innerCertificate z w a b u)[7]?=some 0 := by
  change some ((((((d0_0_1 z w a b u)*(d1_18_6 z w a b u))+((((d0_1_0 z w a b u)*(d1_17_7 z w a b u))+((d0_1_1 z w a b u)*(d1_17_6 z w a b u)))+((((d0_2_0 z w a b u)*(d1_16_7 z w a b u))+((d0_2_1 z w a b u)*(d1_16_6 z w a b u)))+((d0_3_0 z w a b u)*(d1_15_7 z w a b u)))))+((((d2_10_7 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_11_7 z w a b u)*(d3_7_0 z w a b u))+0)+(((d2_12_7 z w a b u)*(d3_6_0 z w a b u))+0))))+((-1)*(d4_18_7 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_15_7,d1_16_6,d1_16_7,d1_17_6,d1_17_7,d1_18_6,d2_10_7,d2_11_7,d2_12_7,d3_6_0,d3_7_0,d3_8_0,d4_18_7]
  ring
#print axioms coefficient_7

theorem coefficient_8 (z w a b u : ℂ) : (innerCertificate z w a b u)[8]?=some 0 := by
  change some (((((d0_1_1 z w a b u)*(d1_17_7 z w a b u))+((d0_2_1 z w a b u)*(d1_16_7 z w a b u)))+((-1)*(d4_18_8 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_1,d0_2_1,d1_16_7,d1_17_7,d4_18_8]
  ring
#print axioms coefficient_8

end SmallLevelTwentySixSource89Split18
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixSource89Split19
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89

theorem coefficient_0 (z w a b u : ℂ) : (innerCertificate z w a b u)[0]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_19_0 z w a b u))+0)+((((d0_1_0 z w a b u)*(d1_18_0 z w a b u))+0)+((((d0_2_0 z w a b u)*(d1_17_0 z w a b u))+0)+(((d0_3_0 z w a b u)*(d1_16_0 z w a b u))+0))))+((((d2_11_0 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_12_0 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_13_0 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_14_0 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_15_0 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_16_0 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_17_0 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_18_0 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_19_0 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+(((-1)*(d4_19_0 z w a b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_1_0,d0_2_0,d0_3_0,d1_16_0,d1_17_0,d1_18_0,d1_19_0,d2_11_0,d2_12_0,d2_13_0,d2_14_0,d2_15_0,d2_16_0,d2_17_0,d2_18_0,d2_19_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_19_0]
  ring
#print axioms coefficient_0

theorem coefficient_1 (z w a b u : ℂ) : (innerCertificate z w a b u)[1]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_19_1 z w a b u))+(((d0_0_1 z w a b u)*(d1_19_0 z w a b u))+0))+((((d0_1_0 z w a b u)*(d1_18_1 z w a b u))+(((d0_1_1 z w a b u)*(d1_18_0 z w a b u))+0))+((((d0_2_0 z w a b u)*(d1_17_1 z w a b u))+(((d0_2_1 z w a b u)*(d1_17_0 z w a b u))+0))+((d0_3_0 z w a b u)*(d1_16_1 z w a b u)))))+((((d2_11_1 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_12_1 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_13_1 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_14_1 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_15_1 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_16_1 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_17_1 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_18_1 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_19_1 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_19_1 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_16_1,d1_17_0,d1_17_1,d1_18_0,d1_18_1,d1_19_0,d1_19_1,d2_11_1,d2_12_1,d2_13_1,d2_14_1,d2_15_1,d2_16_1,d2_17_1,d2_18_1,d2_19_1,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_19_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (z w a b u : ℂ) : (innerCertificate z w a b u)[2]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_19_2 z w a b u))+((d0_0_1 z w a b u)*(d1_19_1 z w a b u)))+((((d0_1_0 z w a b u)*(d1_18_2 z w a b u))+((d0_1_1 z w a b u)*(d1_18_1 z w a b u)))+((((d0_2_0 z w a b u)*(d1_17_2 z w a b u))+((d0_2_1 z w a b u)*(d1_17_1 z w a b u)))+((d0_3_0 z w a b u)*(d1_16_2 z w a b u)))))+((((d2_11_2 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_12_2 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_13_2 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_14_2 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_15_2 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_16_2 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_17_2 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_18_2 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_19_2 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_19_2 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_16_2,d1_17_1,d1_17_2,d1_18_1,d1_18_2,d1_19_1,d1_19_2,d2_11_2,d2_12_2,d2_13_2,d2_14_2,d2_15_2,d2_16_2,d2_17_2,d2_18_2,d2_19_2,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_19_2]
  ring
#print axioms coefficient_2

theorem coefficient_3 (z w a b u : ℂ) : (innerCertificate z w a b u)[3]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_19_3 z w a b u))+((d0_0_1 z w a b u)*(d1_19_2 z w a b u)))+((((d0_1_0 z w a b u)*(d1_18_3 z w a b u))+((d0_1_1 z w a b u)*(d1_18_2 z w a b u)))+((((d0_2_0 z w a b u)*(d1_17_3 z w a b u))+((d0_2_1 z w a b u)*(d1_17_2 z w a b u)))+((d0_3_0 z w a b u)*(d1_16_3 z w a b u)))))+((((d2_11_3 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_12_3 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_13_3 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_14_3 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_15_3 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_16_3 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_17_3 z w a b u)*(d3_2_0 z w a b u))+0)+(((d2_18_3 z w a b u)*(d3_1_0 z w a b u))+0)))))))))+((-1)*(d4_19_3 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_16_3,d1_17_2,d1_17_3,d1_18_2,d1_18_3,d1_19_2,d1_19_3,d2_11_3,d2_12_3,d2_13_3,d2_14_3,d2_15_3,d2_16_3,d2_17_3,d2_18_3,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_19_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (z w a b u : ℂ) : (innerCertificate z w a b u)[4]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_19_4 z w a b u))+((d0_0_1 z w a b u)*(d1_19_3 z w a b u)))+((((d0_1_0 z w a b u)*(d1_18_4 z w a b u))+((d0_1_1 z w a b u)*(d1_18_3 z w a b u)))+((((d0_2_0 z w a b u)*(d1_17_4 z w a b u))+((d0_2_1 z w a b u)*(d1_17_3 z w a b u)))+((d0_3_0 z w a b u)*(d1_16_4 z w a b u)))))+((((d2_11_4 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_12_4 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_13_4 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_14_4 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_15_4 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_16_4 z w a b u)*(d3_3_0 z w a b u))+0)+(((d2_17_4 z w a b u)*(d3_2_0 z w a b u))+0))))))))+((-1)*(d4_19_4 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_16_4,d1_17_3,d1_17_4,d1_18_3,d1_18_4,d1_19_3,d1_19_4,d2_11_4,d2_12_4,d2_13_4,d2_14_4,d2_15_4,d2_16_4,d2_17_4,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_19_4]
  ring
#print axioms coefficient_4

theorem coefficient_5 (z w a b u : ℂ) : (innerCertificate z w a b u)[5]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_19_5 z w a b u))+((d0_0_1 z w a b u)*(d1_19_4 z w a b u)))+((((d0_1_0 z w a b u)*(d1_18_5 z w a b u))+((d0_1_1 z w a b u)*(d1_18_4 z w a b u)))+((((d0_2_0 z w a b u)*(d1_17_5 z w a b u))+((d0_2_1 z w a b u)*(d1_17_4 z w a b u)))+((d0_3_0 z w a b u)*(d1_16_5 z w a b u)))))+((((d2_11_5 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_12_5 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_13_5 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_14_5 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_15_5 z w a b u)*(d3_4_0 z w a b u))+0)+(((d2_16_5 z w a b u)*(d3_3_0 z w a b u))+0)))))))+((-1)*(d4_19_5 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_16_5,d1_17_4,d1_17_5,d1_18_4,d1_18_5,d1_19_4,d1_19_5,d2_11_5,d2_12_5,d2_13_5,d2_14_5,d2_15_5,d2_16_5,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_19_5]
  ring
#print axioms coefficient_5

theorem coefficient_6 (z w a b u : ℂ) : (innerCertificate z w a b u)[6]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_19_6 z w a b u))+((d0_0_1 z w a b u)*(d1_19_5 z w a b u)))+((((d0_1_0 z w a b u)*(d1_18_6 z w a b u))+((d0_1_1 z w a b u)*(d1_18_5 z w a b u)))+((((d0_2_0 z w a b u)*(d1_17_6 z w a b u))+((d0_2_1 z w a b u)*(d1_17_5 z w a b u)))+((d0_3_0 z w a b u)*(d1_16_6 z w a b u)))))+((((d2_11_6 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_12_6 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_13_6 z w a b u)*(d3_6_0 z w a b u))+0)+(((d2_14_6 z w a b u)*(d3_5_0 z w a b u))+0)))))+((-1)*(d4_19_6 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_16_6,d1_17_5,d1_17_6,d1_18_5,d1_18_6,d1_19_5,d1_19_6,d2_11_6,d2_12_6,d2_13_6,d2_14_6,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_19_6]
  ring
#print axioms coefficient_6

theorem coefficient_7 (z w a b u : ℂ) : (innerCertificate z w a b u)[7]?=some 0 := by
  change some ((((((d0_0_1 z w a b u)*(d1_19_6 z w a b u))+(((d0_1_1 z w a b u)*(d1_18_6 z w a b u))+((((d0_2_0 z w a b u)*(d1_17_7 z w a b u))+((d0_2_1 z w a b u)*(d1_17_6 z w a b u)))+((d0_3_0 z w a b u)*(d1_16_7 z w a b u)))))+((((d2_11_7 z w a b u)*(d3_8_0 z w a b u))+0)+(((d2_12_7 z w a b u)*(d3_7_0 z w a b u))+0)))+((-1)*(d4_19_7 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_1,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_16_7,d1_17_6,d1_17_7,d1_18_6,d1_19_6,d2_11_7,d2_12_7,d3_7_0,d3_8_0,d4_19_7]
  ring
#print axioms coefficient_7

theorem coefficient_8 (z w a b u : ℂ) : (innerCertificate z w a b u)[8]?=some 0 := by
  change some ((((d0_2_1 z w a b u)*(d1_17_7 z w a b u))+((-1)*(d4_19_8 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_2_1,d1_17_7,d4_19_8]
  ring
#print axioms coefficient_8

end SmallLevelTwentySixSource89Split19
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixSource89Split20
open SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixSourceResultant89

theorem coefficient_0 (z w a b u : ℂ) : (innerCertificate z w a b u)[0]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_20_0 z w a b u))+0)+((((d0_1_0 z w a b u)*(d1_19_0 z w a b u))+0)+((((d0_2_0 z w a b u)*(d1_18_0 z w a b u))+0)+(((d0_3_0 z w a b u)*(d1_17_0 z w a b u))+0))))+((((d2_12_0 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_13_0 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_14_0 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_15_0 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_16_0 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_17_0 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_18_0 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_19_0 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_20_0 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+(((-1)*(d4_20_0 z w a b u))+0)))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_1_0,d0_2_0,d0_3_0,d1_17_0,d1_18_0,d1_19_0,d1_20_0,d2_12_0,d2_13_0,d2_14_0,d2_15_0,d2_16_0,d2_17_0,d2_18_0,d2_19_0,d2_20_0,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_20_0]
  ring
#print axioms coefficient_0

theorem coefficient_1 (z w a b u : ℂ) : (innerCertificate z w a b u)[1]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_20_1 z w a b u))+(((d0_0_1 z w a b u)*(d1_20_0 z w a b u))+0))+((((d0_1_0 z w a b u)*(d1_19_1 z w a b u))+(((d0_1_1 z w a b u)*(d1_19_0 z w a b u))+0))+((((d0_2_0 z w a b u)*(d1_18_1 z w a b u))+(((d0_2_1 z w a b u)*(d1_18_0 z w a b u))+0))+((d0_3_0 z w a b u)*(d1_17_1 z w a b u)))))+((((d2_12_1 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_13_1 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_14_1 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_15_1 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_16_1 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_17_1 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_18_1 z w a b u)*(d3_2_0 z w a b u))+0)+((((d2_19_1 z w a b u)*(d3_1_0 z w a b u))+0)+(((d2_20_1 z w a b u)*(d3_0_0 z w a b u))+0))))))))))+((-1)*(d4_20_1 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_17_1,d1_18_0,d1_18_1,d1_19_0,d1_19_1,d1_20_0,d1_20_1,d2_12_1,d2_13_1,d2_14_1,d2_15_1,d2_16_1,d2_17_1,d2_18_1,d2_19_1,d2_20_1,d3_0_0,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_20_1]
  ring
#print axioms coefficient_1

theorem coefficient_2 (z w a b u : ℂ) : (innerCertificate z w a b u)[2]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_20_2 z w a b u))+((d0_0_1 z w a b u)*(d1_20_1 z w a b u)))+((((d0_1_0 z w a b u)*(d1_19_2 z w a b u))+((d0_1_1 z w a b u)*(d1_19_1 z w a b u)))+((((d0_2_0 z w a b u)*(d1_18_2 z w a b u))+((d0_2_1 z w a b u)*(d1_18_1 z w a b u)))+((d0_3_0 z w a b u)*(d1_17_2 z w a b u)))))+((((d2_12_2 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_13_2 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_14_2 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_15_2 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_16_2 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_17_2 z w a b u)*(d3_3_0 z w a b u))+0)+((((d2_18_2 z w a b u)*(d3_2_0 z w a b u))+0)+(((d2_19_2 z w a b u)*(d3_1_0 z w a b u))+0)))))))))+((-1)*(d4_20_2 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_17_2,d1_18_1,d1_18_2,d1_19_1,d1_19_2,d1_20_1,d1_20_2,d2_12_2,d2_13_2,d2_14_2,d2_15_2,d2_16_2,d2_17_2,d2_18_2,d2_19_2,d3_1_0,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_20_2]
  ring
#print axioms coefficient_2

theorem coefficient_3 (z w a b u : ℂ) : (innerCertificate z w a b u)[3]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_20_3 z w a b u))+((d0_0_1 z w a b u)*(d1_20_2 z w a b u)))+((((d0_1_0 z w a b u)*(d1_19_3 z w a b u))+((d0_1_1 z w a b u)*(d1_19_2 z w a b u)))+((((d0_2_0 z w a b u)*(d1_18_3 z w a b u))+((d0_2_1 z w a b u)*(d1_18_2 z w a b u)))+((d0_3_0 z w a b u)*(d1_17_3 z w a b u)))))+((((d2_12_3 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_13_3 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_14_3 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_15_3 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_16_3 z w a b u)*(d3_4_0 z w a b u))+0)+((((d2_17_3 z w a b u)*(d3_3_0 z w a b u))+0)+(((d2_18_3 z w a b u)*(d3_2_0 z w a b u))+0))))))))+((-1)*(d4_20_3 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_17_3,d1_18_2,d1_18_3,d1_19_2,d1_19_3,d1_20_2,d1_20_3,d2_12_3,d2_13_3,d2_14_3,d2_15_3,d2_16_3,d2_17_3,d2_18_3,d3_2_0,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_20_3]
  ring
#print axioms coefficient_3

theorem coefficient_4 (z w a b u : ℂ) : (innerCertificate z w a b u)[4]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_20_4 z w a b u))+((d0_0_1 z w a b u)*(d1_20_3 z w a b u)))+((((d0_1_0 z w a b u)*(d1_19_4 z w a b u))+((d0_1_1 z w a b u)*(d1_19_3 z w a b u)))+((((d0_2_0 z w a b u)*(d1_18_4 z w a b u))+((d0_2_1 z w a b u)*(d1_18_3 z w a b u)))+((d0_3_0 z w a b u)*(d1_17_4 z w a b u)))))+((((d2_12_4 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_13_4 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_14_4 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_15_4 z w a b u)*(d3_5_0 z w a b u))+0)+((((d2_16_4 z w a b u)*(d3_4_0 z w a b u))+0)+(((d2_17_4 z w a b u)*(d3_3_0 z w a b u))+0)))))))+((-1)*(d4_20_4 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_17_4,d1_18_3,d1_18_4,d1_19_3,d1_19_4,d1_20_3,d1_20_4,d2_12_4,d2_13_4,d2_14_4,d2_15_4,d2_16_4,d2_17_4,d3_3_0,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_20_4]
  ring
#print axioms coefficient_4

theorem coefficient_5 (z w a b u : ℂ) : (innerCertificate z w a b u)[5]?=some 0 := by
  change some (((((((d0_0_0 z w a b u)*(d1_20_5 z w a b u))+((d0_0_1 z w a b u)*(d1_20_4 z w a b u)))+((((d0_1_0 z w a b u)*(d1_19_5 z w a b u))+((d0_1_1 z w a b u)*(d1_19_4 z w a b u)))+((((d0_2_0 z w a b u)*(d1_18_5 z w a b u))+((d0_2_1 z w a b u)*(d1_18_4 z w a b u)))+((d0_3_0 z w a b u)*(d1_17_5 z w a b u)))))+((((d2_12_5 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_13_5 z w a b u)*(d3_7_0 z w a b u))+0)+((((d2_14_5 z w a b u)*(d3_6_0 z w a b u))+0)+((((d2_15_5 z w a b u)*(d3_5_0 z w a b u))+0)+(((d2_16_5 z w a b u)*(d3_4_0 z w a b u))+0))))))+((-1)*(d4_20_5 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_0,d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_17_5,d1_18_4,d1_18_5,d1_19_4,d1_19_5,d1_20_4,d1_20_5,d2_12_5,d2_13_5,d2_14_5,d2_15_5,d2_16_5,d3_4_0,d3_5_0,d3_6_0,d3_7_0,d3_8_0,d4_20_5]
  ring
#print axioms coefficient_5

theorem coefficient_6 (z w a b u : ℂ) : (innerCertificate z w a b u)[6]?=some 0 := by
  change some ((((((d0_0_1 z w a b u)*(d1_20_5 z w a b u))+((((d0_1_0 z w a b u)*(d1_19_6 z w a b u))+((d0_1_1 z w a b u)*(d1_19_5 z w a b u)))+((((d0_2_0 z w a b u)*(d1_18_6 z w a b u))+((d0_2_1 z w a b u)*(d1_18_5 z w a b u)))+((d0_3_0 z w a b u)*(d1_17_6 z w a b u)))))+((((d2_12_6 z w a b u)*(d3_8_0 z w a b u))+0)+((((d2_13_6 z w a b u)*(d3_7_0 z w a b u))+0)+(((d2_14_6 z w a b u)*(d3_6_0 z w a b u))+0))))+((-1)*(d4_20_6 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_0_1,d0_1_0,d0_1_1,d0_2_0,d0_2_1,d0_3_0,d1_17_6,d1_18_5,d1_18_6,d1_19_5,d1_19_6,d1_20_5,d2_12_6,d2_13_6,d2_14_6,d3_6_0,d3_7_0,d3_8_0,d4_20_6]
  ring
#print axioms coefficient_6

theorem coefficient_7 (z w a b u : ℂ) : (innerCertificate z w a b u)[7]?=some 0 := by
  change some ((((((d0_1_1 z w a b u)*(d1_19_6 z w a b u))+(((d0_2_1 z w a b u)*(d1_18_6 z w a b u))+((d0_3_0 z w a b u)*(d1_17_7 z w a b u))))+(((d2_12_7 z w a b u)*(d3_8_0 z w a b u))+0))+((-1)*(d4_20_7 z w a b u))))=some (0:ℂ)
  apply congrArg some
  simp only [d0_1_1,d0_2_1,d0_3_0,d1_17_7,d1_18_6,d1_19_6,d2_12_7,d3_8_0,d4_20_7]
  ring
#print axioms coefficient_7

end SmallLevelTwentySixSource89Split20
end

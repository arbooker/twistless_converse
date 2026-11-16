module
public meta import SmallLevelCertificateBatchCommandV1
public import SmallLevelTwentySixSourceIndexSplitIndexDataSeriesV4
-- Bounded certificate elaboration.
set_option Elab.async false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
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

certificate_batch {
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

}

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

certificate_batch {
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

}

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

certificate_batch {
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

}

end SmallLevelTwentySixSource89Split14
end


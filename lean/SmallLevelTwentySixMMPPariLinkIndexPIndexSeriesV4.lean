module
public import QuantitativeArithmeticPolynomialHornerBridgeV1
public import SmallLevelTwentySixMMPPariLinkIndexPIndexDataSeriesV4
public import SmallLevelTwentySixMMPPariLinkIndexPIndexRightXBundleSeriesV4
public import SmallLevelTwentySixMMPPariLinkIndexPIndexLeftXBundleSeriesV4
public import SmallLevelTwentySixMMPPariTraceIndexSeriesV4
public import SmallLevelTwentySixMMPPariTraceIndexFamilySeriesV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink002P1
open SmallLevelPolynomialCoefficientCertificate
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace002.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace001.p4 x y z w a b u := by
  rfl
#print axioms binding

end SmallLevelTwentySixMMPPariLink002P1
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink003P1
open SmallLevelPolynomialCoefficientCertificate
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace003.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace001.p1 x y z w a b u := by
  rfl
#print axioms binding

end SmallLevelTwentySixMMPPariLink003P1
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink004P1
open SmallLevelPolynomialCoefficientCertificate
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace004.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace003.p4 x y z w a b u := by
  rfl
#print axioms binding

end SmallLevelTwentySixMMPPariLink004P1
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink008P1
open SmallLevelPolynomialCoefficientCertificate
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace008.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace007.p4 x y z w a b u := by
  rfl
#print axioms binding

end SmallLevelTwentySixMMPPariLink008P1
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink011P1
open SmallLevelPolynomialCoefficientCertificate
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace011.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace010.p4 x y z w a b u := by
  rfl
#print axioms binding

end SmallLevelTwentySixMMPPariLink011P1
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink013P1
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace013.p1 x y z w a b u=canonical x y z w a b u := by
  rfl
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace012.p4 x y z w a b u=canonical x y z w a b u := by
  simp only [SmallLevelTwentySixMMPPariTrace012.p4,SmallLevelTwentySixMMPPariTrace012.coefficients4,canonical,right_coefficient_0,right_coefficient_1,right_coefficient_2,right_coefficient_3,right_coefficient_4,right_coefficient_5,right_coefficient_6,right_coefficient_7,right_coefficient_8,right_coefficient_9,right_coefficient_10,right_coefficient_11,right_coefficient_12,right_coefficient_13,right_coefficient_14,right_coefficient_15,right_coefficient_16,right_coefficient_17,right_coefficient_18]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace013.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace012.p4 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink013P1
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink015P1
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace015.p1 x y z w a b u=canonical x y z w a b u := by
  rfl
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace014.p4 x y z w a b u=canonical x y z w a b u := by
  simp only [SmallLevelTwentySixMMPPariTrace014.p4,SmallLevelTwentySixMMPPariTrace014.coefficients4,canonical,right_coefficient_0,right_coefficient_1,right_coefficient_2,right_coefficient_3,right_coefficient_4,right_coefficient_5,right_coefficient_6,right_coefficient_7,right_coefficient_8,right_coefficient_9,right_coefficient_10,right_coefficient_11,right_coefficient_12,right_coefficient_13,right_coefficient_14,right_coefficient_15,right_coefficient_16,right_coefficient_17,right_coefficient_18,right_coefficient_19,right_coefficient_20,right_coefficient_21,right_coefficient_22,right_coefficient_23,right_coefficient_24]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace015.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace014.p4 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink015P1
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink018P1
open SmallLevelPolynomialCoefficientCertificate
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace018.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace017.p4 x y z w a b u := by
  rfl
#print axioms binding

end SmallLevelTwentySixMMPPariLink018P1
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink019P1
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace019.p1 x y z w a b u=canonical x y z w a b u := by
  simp only [canonical,SmallLevelTwentySixMMPPariTrace019.p1,QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner,QuantitativeArithmeticPolynomialHornerBridge.rightHorner,canonical0,canonical1,canonical2,canonical3,canonical4,canonical5,canonical6,canonical7,canonical8,canonical9,canonical10,canonical11,canonical12,canonical13,canonical14,canonical15,canonical16,canonical17,canonical18,canonical19,canonical20,canonical21,canonical22,canonical23,canonical24,canonical25,canonical26,canonical27,canonical28,canonical29,canonical30,canonical31,canonical32,zero_mul,zero_add,mul_zero,add_zero,pow_succ,pow_zero,pow_one]
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace018.p6 x y z w a b u=canonical x y z w a b u := by
  rfl
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace019.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace018.p6 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink019P1
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink021P1
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace021.p1 x y z w a b u=canonical x y z w a b u := by
  simp only [canonical,SmallLevelTwentySixMMPPariTrace021.p1,QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner,QuantitativeArithmeticPolynomialHornerBridge.rightHorner,canonical0,canonical1,canonical2,canonical3,canonical4,zero_mul,zero_add,mul_zero,add_zero,pow_succ,pow_zero,pow_one]
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace009.p1 x y z w a b u=canonical x y z w a b u := by
  rfl
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace021.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace009.p1 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink021P1
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink023P1
open SmallLevelPolynomialCoefficientCertificate
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace023.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace022.p4 x y z w a b u := by
  rfl
#print axioms binding

end SmallLevelTwentySixMMPPariLink023P1
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink025P1
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace025.p1 x y z w a b u=canonical x y z w a b u := by
  simp only [SmallLevelTwentySixMMPPariTrace025.p1,SmallLevelTwentySixMMPPariTrace025.coefficients1,canonical,left_coefficient_0,left_coefficient_1,left_coefficient_2,left_coefficient_3,left_coefficient_4,left_coefficient_5,left_coefficient_6,left_coefficient_7,left_coefficient_8,left_coefficient_9,left_coefficient_10,left_coefficient_11,left_coefficient_12,left_coefficient_13,left_coefficient_14,left_coefficient_15,left_coefficient_16,left_coefficient_17,left_coefficient_18,left_coefficient_19,left_coefficient_20,left_coefficient_21]
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace024.p4 x y z w a b u=canonical x y z w a b u := by
  simp only [SmallLevelTwentySixMMPPariTrace024.p4,SmallLevelTwentySixMMPPariTrace024.coefficients4,canonical,right_coefficient_0,right_coefficient_1,right_coefficient_2,right_coefficient_3,right_coefficient_4,right_coefficient_5,right_coefficient_6,right_coefficient_7,right_coefficient_8,right_coefficient_9,right_coefficient_10,right_coefficient_11,right_coefficient_12,right_coefficient_13,right_coefficient_14,right_coefficient_15,right_coefficient_16,right_coefficient_17,right_coefficient_18,right_coefficient_19,right_coefficient_20,right_coefficient_21]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace025.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace024.p4 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink025P1
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink027P1
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace027.p1 x y z w a b u=canonical x y z w a b u := by
  simp only [SmallLevelTwentySixMMPPariTrace027.p1,SmallLevelTwentySixMMPPariTrace027.coefficients1,canonical,left_coefficient_0,left_coefficient_1,left_coefficient_2,left_coefficient_3,left_coefficient_4,left_coefficient_5,left_coefficient_6,left_coefficient_7,left_coefficient_8,left_coefficient_9,left_coefficient_10,left_coefficient_11,left_coefficient_12,left_coefficient_13,left_coefficient_14,left_coefficient_15,left_coefficient_16,left_coefficient_17,left_coefficient_18,left_coefficient_19,left_coefficient_20,left_coefficient_21,left_coefficient_22,left_coefficient_23,left_coefficient_24,left_coefficient_25,left_coefficient_26,left_coefficient_27,left_coefficient_28,left_coefficient_29,left_coefficient_30,left_coefficient_31]
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace026.p4 x y z w a b u=canonical x y z w a b u := by
  simp only [SmallLevelTwentySixMMPPariTrace026.p4,SmallLevelTwentySixMMPPariTrace026.coefficients4,canonical,right_coefficient_0,right_coefficient_1,right_coefficient_2,right_coefficient_3,right_coefficient_4,right_coefficient_5,right_coefficient_6,right_coefficient_7,right_coefficient_8,right_coefficient_9,right_coefficient_10,right_coefficient_11,right_coefficient_12,right_coefficient_13,right_coefficient_14,right_coefficient_15,right_coefficient_16,right_coefficient_17,right_coefficient_18,right_coefficient_19,right_coefficient_20,right_coefficient_21,right_coefficient_22,right_coefficient_23,right_coefficient_24,right_coefficient_25,right_coefficient_26,right_coefficient_27,right_coefficient_28,right_coefficient_29,right_coefficient_30,right_coefficient_31]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace027.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace026.p4 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink027P1
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink030P1
open SmallLevelPolynomialCoefficientCertificate
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace030.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace029.p4 x y z w a b u := by
  rfl
#print axioms binding

end SmallLevelTwentySixMMPPariLink030P1
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink031P1
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace031.p1 x y z w a b u=canonical x y z w a b u := by
  simp only [canonical,SmallLevelTwentySixMMPPariTrace031.p1,QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner,QuantitativeArithmeticPolynomialHornerBridge.rightHorner,canonical0,canonical1,canonical2,canonical3,canonical4,canonical5,canonical6,canonical7,canonical8,canonical9,canonical10,canonical11,canonical12,canonical13,canonical14,canonical15,canonical16,canonical17,canonical18,canonical19,canonical20,canonical21,canonical22,canonical23,canonical24,canonical25,canonical26,canonical27,canonical28,canonical29,canonical30,canonical31,canonical32,canonical33,canonical34,canonical35,canonical36,canonical37,canonical38,canonical39,canonical40,canonical41,zero_mul,zero_add,mul_zero,add_zero,pow_succ,pow_zero,pow_one]
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace030.p6 x y z w a b u=canonical x y z w a b u := by
  rfl
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace031.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace030.p6 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink031P1
end

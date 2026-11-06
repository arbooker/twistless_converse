module
public import QuantitativeArithmeticPolynomialHornerBridgeV1
public import SmallLevelTwentySixMMPPariLinkIndexPIndexDataSeriesV4
public import SmallLevelTwentySixMMPPariLinkIndexPIndexLeftXBundleSeriesV4
public import SmallLevelTwentySixMMPPariLinkIndexPIndexRightXBundleSeriesV4
public import SmallLevelTwentySixMMPPariTraceIndexSeriesV4
public import SmallLevelTwentySixMMPPariTraceIndexFamilySeriesV4
@[expose] public noncomputable section
section
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink005P1
open SmallLevelPolynomialCoefficientCertificate
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace005.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace004.p6 x y z w a b u := by
  rfl
#print axioms binding

end SmallLevelTwentySixMMPPariLink005P1
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

namespace SmallLevelTwentySixMMPPariLink005P3
open SmallLevelPolynomialCoefficientCertificate
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace005.p3 x y z w a b u=SmallLevelTwentySixMMPPariTrace002.p6 x y z w a b u := by
  rfl
#print axioms binding

end SmallLevelTwentySixMMPPariLink005P3
end
end

section
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink010P1
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace010.p1 x y z w a b u=canonical x y z w a b u := by
  rfl
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace007.p1 x y z w a b u=canonical x y z w a b u := by
  simp only [canonical,SmallLevelTwentySixMMPPariTrace007.p1,QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner,QuantitativeArithmeticPolynomialHornerBridge.rightHorner,canonical0,canonical1,canonical2,zero_mul,zero_add,mul_zero,add_zero,pow_succ,pow_zero,pow_one]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace010.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace007.p1 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink010P1
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

namespace SmallLevelTwentySixMMPPariLink010P3
open SmallLevelPolynomialCoefficientCertificate
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace010.p3 x y z w a b u=SmallLevelTwentySixMMPPariTrace009.p4 x y z w a b u := by
  rfl
#print axioms binding

end SmallLevelTwentySixMMPPariLink010P3
end
end

section
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink012P1
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace012.p1 x y z w a b u=canonical x y z w a b u := by
  simp only [SmallLevelTwentySixMMPPariTrace012.p1,SmallLevelTwentySixMMPPariTrace012.coefficients1,canonical,left_coefficient_0,left_coefficient_1,left_coefficient_2,left_coefficient_3,left_coefficient_4,left_coefficient_5]
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace008.p6 x y z w a b u=canonical x y z w a b u := by
  simp only [canonical,SmallLevelTwentySixMMPPariTrace008.p6,QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner,QuantitativeArithmeticPolynomialHornerBridge.rightHorner,canonical0,canonical1,canonical2,canonical3,canonical4,canonical5,zero_mul,zero_add,mul_zero,add_zero,pow_succ,pow_zero,pow_one]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace012.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace008.p6 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink012P1
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

namespace SmallLevelTwentySixMMPPariLink012P3
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace012.p3 x y z w a b u=canonical x y z w a b u := by
  simp only [SmallLevelTwentySixMMPPariTrace012.p3,SmallLevelTwentySixMMPPariTrace012.coefficients3,canonical,left_coefficient_0,left_coefficient_1,left_coefficient_2,left_coefficient_3,left_coefficient_4,left_coefficient_5,left_coefficient_6,left_coefficient_7,left_coefficient_8,left_coefficient_9,left_coefficient_10,left_coefficient_11,left_coefficient_12,left_coefficient_13,left_coefficient_14,left_coefficient_15,left_coefficient_16]
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace011.p6 x y z w a b u=canonical x y z w a b u := by
  rfl
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace012.p3 x y z w a b u=SmallLevelTwentySixMMPPariTrace011.p6 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink012P3
end
end

section
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink014P1
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace014.p1 x y z w a b u=canonical x y z w a b u := by
  simp only [SmallLevelTwentySixMMPPariTrace014.p1,SmallLevelTwentySixMMPPariTrace014.coefficients1,canonical,left_coefficient_0,left_coefficient_1,left_coefficient_2,left_coefficient_3]
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace001.p1 x y z w a b u=canonical x y z w a b u := by
  simp only [canonical,SmallLevelTwentySixMMPPariTrace001.p1,QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner,QuantitativeArithmeticPolynomialHornerBridge.rightHorner,canonical0,canonical1,canonical2,canonical3,zero_mul,zero_add,mul_zero,add_zero,pow_succ,pow_zero,pow_one]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace014.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace001.p1 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink014P1
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

namespace SmallLevelTwentySixMMPPariLink014P3
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace014.p3 x y z w a b u=canonical x y z w a b u := by
  simp only [SmallLevelTwentySixMMPPariTrace014.p3,SmallLevelTwentySixMMPPariTrace014.coefficients3,canonical,left_coefficient_0,left_coefficient_1,left_coefficient_2,left_coefficient_3,left_coefficient_4,left_coefficient_5,left_coefficient_6,left_coefficient_7,left_coefficient_8,left_coefficient_9,left_coefficient_10,left_coefficient_11,left_coefficient_12,left_coefficient_13,left_coefficient_14,left_coefficient_15,left_coefficient_16,left_coefficient_17]
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace013.p6 x y z w a b u=canonical x y z w a b u := by
  rfl
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace014.p3 x y z w a b u=SmallLevelTwentySixMMPPariTrace013.p6 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink014P3
end
end

section
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink016P1
open SmallLevelPolynomialCoefficientCertificate
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace016.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace015.p6 x y z w a b u := by
  rfl
#print axioms binding

end SmallLevelTwentySixMMPPariLink016P1
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

namespace SmallLevelTwentySixMMPPariLink016P3
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace016.p3 x y z w a b u=canonical x y z w a b u := by
  rfl
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace002.p6 x y z w a b u=canonical x y z w a b u := by
  simp only [canonical,SmallLevelTwentySixMMPPariTrace002.p6,QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner,QuantitativeArithmeticPolynomialHornerBridge.rightHorner,canonical0,canonical1,canonical2,canonical3,canonical4,zero_mul,zero_add,mul_zero,add_zero,pow_succ,pow_zero,pow_one]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace016.p3 x y z w a b u=SmallLevelTwentySixMMPPariTrace002.p6 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink016P3
end
end

section
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink017P1
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace017.p1 x y z w a b u=canonical x y z w a b u := by
  rfl
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace005.p4 x y z w a b u=canonical x y z w a b u := by
  simp only [canonical,SmallLevelTwentySixMMPPariTrace005.p4,QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner,QuantitativeArithmeticPolynomialHornerBridge.rightHorner,canonical0,canonical1,canonical2,canonical3,canonical4,canonical5,canonical6,zero_mul,zero_add,mul_zero,add_zero,pow_succ,pow_zero,pow_one]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace017.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace005.p4 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink017P1
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

namespace SmallLevelTwentySixMMPPariLink017P3
open SmallLevelPolynomialCoefficientCertificate
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace017.p3 x y z w a b u=SmallLevelTwentySixMMPPariTrace016.p4 x y z w a b u := by
  rfl
#print axioms binding

end SmallLevelTwentySixMMPPariLink017P3
end
end

section
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink022P1
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace022.p1 x y z w a b u=canonical x y z w a b u := by
  rfl
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace007.p1 x y z w a b u=canonical x y z w a b u := by
  simp only [canonical,SmallLevelTwentySixMMPPariTrace007.p1,QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner,QuantitativeArithmeticPolynomialHornerBridge.rightHorner,canonical0,canonical1,canonical2,zero_mul,zero_add,mul_zero,add_zero,pow_succ,pow_zero,pow_one]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace022.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace007.p1 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink022P1
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

namespace SmallLevelTwentySixMMPPariLink022P3
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace022.p3 x y z w a b u=canonical x y z w a b u := by
  rfl
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace021.p4 x y z w a b u=canonical x y z w a b u := by
  simp only [canonical,SmallLevelTwentySixMMPPariTrace021.p4,SmallLevelTwentySixMMPPariTrace021.p3,QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner,QuantitativeArithmeticPolynomialHornerBridge.rightHorner,canonical0,canonical1,canonical2,canonical3,canonical4,canonical5,canonical6,canonical7,canonical8,canonical9,canonical10,canonical11,canonical12,canonical13,canonical14,zero_mul,zero_add,mul_zero,add_zero,pow_succ,pow_zero,pow_one]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace022.p3 x y z w a b u=SmallLevelTwentySixMMPPariTrace021.p4 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink022P3
end
end

section
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink024P1
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace024.p1 x y z w a b u=canonical x y z w a b u := by
  simp only [SmallLevelTwentySixMMPPariTrace024.p1,SmallLevelTwentySixMMPPariTrace024.coefficients1,canonical,left_coefficient_0,left_coefficient_1,left_coefficient_2,left_coefficient_3,left_coefficient_4,left_coefficient_5]
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace008.p6 x y z w a b u=canonical x y z w a b u := by
  simp only [canonical,SmallLevelTwentySixMMPPariTrace008.p6,QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner,QuantitativeArithmeticPolynomialHornerBridge.rightHorner,canonical0,canonical1,canonical2,canonical3,canonical4,canonical5,zero_mul,zero_add,mul_zero,add_zero,pow_succ,pow_zero,pow_one]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace024.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace008.p6 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink024P1
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

namespace SmallLevelTwentySixMMPPariLink024P3
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace024.p3 x y z w a b u=canonical x y z w a b u := by
  simp only [SmallLevelTwentySixMMPPariTrace024.p3,SmallLevelTwentySixMMPPariTrace024.coefficients3,canonical,left_coefficient_0,left_coefficient_1,left_coefficient_2,left_coefficient_3,left_coefficient_4,left_coefficient_5,left_coefficient_6,left_coefficient_7,left_coefficient_8,left_coefficient_9,left_coefficient_10,left_coefficient_11,left_coefficient_12,left_coefficient_13,left_coefficient_14,left_coefficient_15]
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace023.p6 x y z w a b u=canonical x y z w a b u := by
  rfl
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace024.p3 x y z w a b u=SmallLevelTwentySixMMPPariTrace023.p6 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink024P3
end
end

section
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink026P1
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace026.p1 x y z w a b u=canonical x y z w a b u := by
  simp only [SmallLevelTwentySixMMPPariTrace026.p1,SmallLevelTwentySixMMPPariTrace026.coefficients1,canonical,left_coefficient_0,left_coefficient_1,left_coefficient_2,left_coefficient_3]
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace001.p1 x y z w a b u=canonical x y z w a b u := by
  simp only [canonical,SmallLevelTwentySixMMPPariTrace001.p1,QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner,QuantitativeArithmeticPolynomialHornerBridge.rightHorner,canonical0,canonical1,canonical2,canonical3,zero_mul,zero_add,mul_zero,add_zero,pow_succ,pow_zero,pow_one]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace026.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace001.p1 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink026P1
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

namespace SmallLevelTwentySixMMPPariLink026P3
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace026.p3 x y z w a b u=canonical x y z w a b u := by
  simp only [SmallLevelTwentySixMMPPariTrace026.p3,SmallLevelTwentySixMMPPariTrace026.coefficients3,canonical,left_coefficient_0,left_coefficient_1,left_coefficient_2,left_coefficient_3,left_coefficient_4,left_coefficient_5,left_coefficient_6,left_coefficient_7,left_coefficient_8,left_coefficient_9,left_coefficient_10,left_coefficient_11,left_coefficient_12,left_coefficient_13,left_coefficient_14,left_coefficient_15,left_coefficient_16,left_coefficient_17,left_coefficient_18,left_coefficient_19]
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace025.p6 x y z w a b u=canonical x y z w a b u := by
  simp only [SmallLevelTwentySixMMPPariTrace025.p6,SmallLevelTwentySixMMPPariTrace025.coefficients6,canonical,right_coefficient_0,right_coefficient_1,right_coefficient_2,right_coefficient_3,right_coefficient_4,right_coefficient_5,right_coefficient_6,right_coefficient_7,right_coefficient_8,right_coefficient_9,right_coefficient_10,right_coefficient_11,right_coefficient_12,right_coefficient_13,right_coefficient_14,right_coefficient_15,right_coefficient_16,right_coefficient_17,right_coefficient_18,right_coefficient_19]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace026.p3 x y z w a b u=SmallLevelTwentySixMMPPariTrace025.p6 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink026P3
end
end

section
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink028P1
open SmallLevelPolynomialCoefficientCertificate
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace028.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace027.p6 x y z w a b u := by
  rfl
#print axioms binding

end SmallLevelTwentySixMMPPariLink028P1
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

namespace SmallLevelTwentySixMMPPariLink028P3
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace028.p3 x y z w a b u=canonical x y z w a b u := by
  rfl
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace002.p6 x y z w a b u=canonical x y z w a b u := by
  simp only [canonical,SmallLevelTwentySixMMPPariTrace002.p6,QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner,QuantitativeArithmeticPolynomialHornerBridge.rightHorner,canonical0,canonical1,canonical2,canonical3,canonical4,zero_mul,zero_add,mul_zero,add_zero,pow_succ,pow_zero,pow_one]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace028.p3 x y z w a b u=SmallLevelTwentySixMMPPariTrace002.p6 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink028P3
end
end

section
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariLink029P1
open SmallLevelPolynomialCoefficientCertificate
theorem left_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace029.p1 x y z w a b u=canonical x y z w a b u := by
  rfl
theorem right_canonical (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace005.p4 x y z w a b u=canonical x y z w a b u := by
  simp only [canonical,SmallLevelTwentySixMMPPariTrace005.p4,QuantitativeArithmeticPolynomialHornerBridge.evaluate_eq_rightHorner,QuantitativeArithmeticPolynomialHornerBridge.rightHorner,canonical0,canonical1,canonical2,canonical3,canonical4,canonical5,canonical6,zero_mul,zero_add,mul_zero,add_zero,pow_succ,pow_zero,pow_one]
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace029.p1 x y z w a b u=SmallLevelTwentySixMMPPariTrace005.p4 x y z w a b u := by
  exact (left_canonical x y z w a b u).trans (right_canonical x y z w a b u).symm
#print axioms binding

end SmallLevelTwentySixMMPPariLink029P1
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

namespace SmallLevelTwentySixMMPPariLink029P3
open SmallLevelPolynomialCoefficientCertificate
theorem binding (x y z w a b u : ℂ) : SmallLevelTwentySixMMPPariTrace029.p3 x y z w a b u=SmallLevelTwentySixMMPPariTrace028.p4 x y z w a b u := by
  rfl
#print axioms binding

end SmallLevelTwentySixMMPPariLink029P3
end
end

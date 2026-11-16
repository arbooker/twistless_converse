module
public import QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateRootMergesSixthStagesV1
public import QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateTheoryV4
public meta import QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateComputeTheoryV4
public meta import QuantitativeArithmeticSparsePolynomialCertificateTheoryV4
public meta import SmallLevelCertificateBatchCommandV1
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificate
open QuantitativeArithmeticSparsePolynomialCertificate
certificate_batch {
def staged_normal1_111110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_111110_staged : normal1_111110 = staged_normal1_111110 := by
  have h : mergeFuel 5000 normal1_1111100 normal1_1111101 = staged_normal1_111110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_1111100) (Eq.refl normal1_1111101)).trans h
#print axioms normal1_111110_staged


def staged_normal1_111111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_111111_staged : normal1_111111 = staged_normal1_111111 := by
  have h : mergeFuel 5000 normal1_1111110 normal1_1111111 = staged_normal1_111111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_1111110) (Eq.refl normal1_1111111)).trans h
#print axioms normal1_111111_staged


def staged_normal1_11111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_11111_staged : normal1_11111 = staged_normal1_11111 := by
  have h : mergeFuel 5000 staged_normal1_111110 staged_normal1_111111 = staged_normal1_11111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_111110_staged normal1_111111_staged).trans h
#print axioms normal1_11111_staged


def staged_normal1_1111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1111_staged : normal1_1111 = staged_normal1_1111 := by
  have h : mergeFuel 5000 staged_normal1_11110 staged_normal1_11111 = staged_normal1_1111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_11110_staged normal1_11111_staged).trans h
#print axioms normal1_1111_staged


def staged_normal1_111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_111_staged : normal1_111 = staged_normal1_111 := by
  have h : mergeFuel 5000 staged_normal1_1110 staged_normal1_1111 = staged_normal1_111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_1110_staged normal1_1111_staged).trans h
#print axioms normal1_111_staged


def staged_normal1_11 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_11_staged : normal1_11 = staged_normal1_11 := by
  have h : mergeFuel 5000 staged_normal1_110 staged_normal1_111 = staged_normal1_11 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_110_staged normal1_111_staged).trans h
#print axioms normal1_11_staged


def staged_normal1_1 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1_staged : normal1_1 = staged_normal1_1 := by
  have h : mergeFuel 5000 staged_normal1_10 staged_normal1_11 = staged_normal1_1 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_10_staged normal1_11_staged).trans h
#print axioms normal1_1_staged


def staged_normal1_root : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_root_staged : normal1_root = staged_normal1_root := by
  have h : mergeFuel 5000 staged_normal1_0 staged_normal1_1 = staged_normal1_root := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_0_staged normal1_1_staged).trans h
#print axioms normal1_root_staged

theorem normal0_root_target : normal0_root = target0 :=
  normal0_root_staged.trans (by decide +kernel)
#print axioms normal0_root_target
theorem normal1_root_target : normal1_root = target1 :=
  normal1_root_staged.trans (by decide +kernel)
#print axioms normal1_root_target

}
end QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificate
end

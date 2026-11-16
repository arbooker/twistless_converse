module
public import QuantitativeArithmeticSmallLevelNineteenFinalCertificateRootMergesFirstStagesV1
public import QuantitativeArithmeticSmallLevelNineteenFinalCertificateTheoryV4
public meta import QuantitativeArithmeticSmallLevelNineteenFinalCertificateComputeTheoryV4
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
namespace QuantitativeArithmeticSmallLevelNineteenFinalCertificate
open QuantitativeArithmeticSparsePolynomialCertificate
certificate_batch {
def staged_normal1_0001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,false,false,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_0001_staged : normal1_0001 = staged_normal1_0001 := by
  have h : mergeFuel 5000 normal1_00010 normal1_00011 = staged_normal1_0001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_00010) (Eq.refl normal1_00011)).trans h
#print axioms normal1_0001_staged


def staged_normal1_000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,false,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_000_staged : normal1_000 = staged_normal1_000 := by
  have h : mergeFuel 5000 staged_normal1_0000 staged_normal1_0001 = staged_normal1_000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_0000_staged normal1_0001_staged).trans h
#print axioms normal1_000_staged


def staged_normal1_0010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,false,true,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_0010_staged : normal1_0010 = staged_normal1_0010 := by
  have h : mergeFuel 5000 normal1_00100 normal1_00101 = staged_normal1_0010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_00100) (Eq.refl normal1_00101)).trans h
#print axioms normal1_0010_staged


def staged_normal1_0011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,false,true,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_0011_staged : normal1_0011 = staged_normal1_0011 := by
  have h : mergeFuel 5000 normal1_00110 normal1_00111 = staged_normal1_0011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_00110) (Eq.refl normal1_00111)).trans h
#print axioms normal1_0011_staged


def staged_normal1_001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,false,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_001_staged : normal1_001 = staged_normal1_001 := by
  have h : mergeFuel 5000 staged_normal1_0010 staged_normal1_0011 = staged_normal1_001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_0010_staged normal1_0011_staged).trans h
#print axioms normal1_001_staged


def staged_normal1_00 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_00_staged : normal1_00 = staged_normal1_00 := by
  have h : mergeFuel 5000 staged_normal1_000 staged_normal1_001 = staged_normal1_00 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_000_staged normal1_001_staged).trans h
#print axioms normal1_00_staged


def staged_normal1_0100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,true,false,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_0100_staged : normal1_0100 = staged_normal1_0100 := by
  have h : mergeFuel 5000 normal1_01000 normal1_01001 = staged_normal1_0100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_01000) (Eq.refl normal1_01001)).trans h
#print axioms normal1_0100_staged


def staged_normal1_0101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,true,false,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_0101_staged : normal1_0101 = staged_normal1_0101 := by
  have h : mergeFuel 5000 normal1_01010 normal1_01011 = staged_normal1_0101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_01010) (Eq.refl normal1_01011)).trans h
#print axioms normal1_0101_staged


def staged_normal1_010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,true,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_010_staged : normal1_010 = staged_normal1_010 := by
  have h : mergeFuel 5000 staged_normal1_0100 staged_normal1_0101 = staged_normal1_010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_0100_staged normal1_0101_staged).trans h
#print axioms normal1_010_staged


def staged_normal1_0110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,true,true,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_0110_staged : normal1_0110 = staged_normal1_0110 := by
  have h : mergeFuel 5000 normal1_01100 normal1_01101 = staged_normal1_0110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_01100) (Eq.refl normal1_01101)).trans h
#print axioms normal1_0110_staged


def staged_normal1_0111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,true,true,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_0111_staged : normal1_0111 = staged_normal1_0111 := by
  have h : mergeFuel 5000 normal1_01110 normal1_01111 = staged_normal1_0111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_01110) (Eq.refl normal1_01111)).trans h
#print axioms normal1_0111_staged


def staged_normal1_011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,true,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_011_staged : normal1_011 = staged_normal1_011 := by
  have h : mergeFuel 5000 staged_normal1_0110 staged_normal1_0111 = staged_normal1_011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_0110_staged normal1_0111_staged).trans h
#print axioms normal1_011_staged


def staged_normal1_01 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_01_staged : normal1_01 = staged_normal1_01 := by
  have h : mergeFuel 5000 staged_normal1_010 staged_normal1_011 = staged_normal1_01 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_010_staged normal1_011_staged).trans h
#print axioms normal1_01_staged


def staged_normal1_0 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_0_staged : normal1_0 = staged_normal1_0 := by
  have h : mergeFuel 5000 staged_normal1_00 staged_normal1_01 = staged_normal1_0 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_00_staged normal1_01_staged).trans h
#print axioms normal1_0_staged


def staged_normal1_1000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,false,false,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_1000_staged : normal1_1000 = staged_normal1_1000 := by
  have h : mergeFuel 5000 normal1_10000 normal1_10001 = staged_normal1_1000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_10000) (Eq.refl normal1_10001)).trans h
#print axioms normal1_1000_staged


def staged_normal1_1001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,false,false,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_1001_staged : normal1_1001 = staged_normal1_1001 := by
  have h : mergeFuel 5000 normal1_10010 normal1_10011 = staged_normal1_1001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_10010) (Eq.refl normal1_10011)).trans h
#print axioms normal1_1001_staged


def staged_normal1_100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,false,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_100_staged : normal1_100 = staged_normal1_100 := by
  have h : mergeFuel 5000 staged_normal1_1000 staged_normal1_1001 = staged_normal1_100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_1000_staged normal1_1001_staged).trans h
#print axioms normal1_100_staged


def staged_normal1_1010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,false,true,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_1010_staged : normal1_1010 = staged_normal1_1010 := by
  have h : mergeFuel 5000 normal1_10100 normal1_10101 = staged_normal1_1010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_10100) (Eq.refl normal1_10101)).trans h
#print axioms normal1_1010_staged


def staged_normal1_1011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,false,true,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_1011_staged : normal1_1011 = staged_normal1_1011 := by
  have h : mergeFuel 5000 normal1_10110 normal1_10111 = staged_normal1_1011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_10110) (Eq.refl normal1_10111)).trans h
#print axioms normal1_1011_staged


def staged_normal1_101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,false,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_101_staged : normal1_101 = staged_normal1_101 := by
  have h : mergeFuel 5000 staged_normal1_1010 staged_normal1_1011 = staged_normal1_101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_1010_staged normal1_1011_staged).trans h
#print axioms normal1_101_staged


def staged_normal1_10 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_10_staged : normal1_10 = staged_normal1_10 := by
  have h : mergeFuel 5000 staged_normal1_100 staged_normal1_101 = staged_normal1_10 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_100_staged normal1_101_staged).trans h
#print axioms normal1_10_staged


def staged_normal1_1100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,true,false,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_1100_staged : normal1_1100 = staged_normal1_1100 := by
  have h : mergeFuel 5000 normal1_11000 normal1_11001 = staged_normal1_1100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_11000) (Eq.refl normal1_11001)).trans h
#print axioms normal1_1100_staged


def staged_normal1_1101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,true,false,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_1101_staged : normal1_1101 = staged_normal1_1101 := by
  have h : mergeFuel 5000 normal1_11010 normal1_11011 = staged_normal1_1101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_11010) (Eq.refl normal1_11011)).trans h
#print axioms normal1_1101_staged


def staged_normal1_110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,true,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_110_staged : normal1_110 = staged_normal1_110 := by
  have h : mergeFuel 5000 staged_normal1_1100 staged_normal1_1101 = staged_normal1_110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_1100_staged normal1_1101_staged).trans h
#print axioms normal1_110_staged


def staged_normal1_1110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,true,true,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_1110_staged : normal1_1110 = staged_normal1_1110 := by
  have h : mergeFuel 5000 normal1_11100 normal1_11101 = staged_normal1_1110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_11100) (Eq.refl normal1_11101)).trans h
#print axioms normal1_1110_staged


def staged_normal1_1111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,true,true,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_1111_staged : normal1_1111 = staged_normal1_1111 := by
  have h : mergeFuel 5000 normal1_11110 normal1_11111 = staged_normal1_1111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_11110) (Eq.refl normal1_11111)).trans h
#print axioms normal1_1111_staged


def staged_normal1_111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,true,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_111_staged : normal1_111 = staged_normal1_111 := by
  have h : mergeFuel 5000 staged_normal1_1110 staged_normal1_1111 = staged_normal1_111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_1110_staged normal1_1111_staged).trans h
#print axioms normal1_111_staged


def staged_normal1_11 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_11_staged : normal1_11 = staged_normal1_11 := by
  have h : mergeFuel 5000 staged_normal1_110 staged_normal1_111 = staged_normal1_11 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_110_staged normal1_111_staged).trans h
#print axioms normal1_11_staged


def staged_normal1_1 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_1_staged : normal1_1 = staged_normal1_1 := by
  have h : mergeFuel 5000 staged_normal1_10 staged_normal1_11 = staged_normal1_1 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_10_staged normal1_11_staged).trans h
#print axioms normal1_1_staged


def staged_normal1_root : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
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
end QuantitativeArithmeticSmallLevelNineteenFinalCertificate
end

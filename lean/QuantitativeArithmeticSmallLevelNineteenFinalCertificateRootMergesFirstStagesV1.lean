module
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
def staged_normal0_0000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,false,false,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_0000_staged : normal0_0000 = staged_normal0_0000 := by
  have h : mergeFuel 5000 normal0_00000 normal0_00001 = staged_normal0_0000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_00000) (Eq.refl normal0_00001)).trans h
#print axioms normal0_0000_staged


def staged_normal0_0001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,false,false,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_0001_staged : normal0_0001 = staged_normal0_0001 := by
  have h : mergeFuel 5000 normal0_00010 normal0_00011 = staged_normal0_0001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_00010) (Eq.refl normal0_00011)).trans h
#print axioms normal0_0001_staged


def staged_normal0_000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,false,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_000_staged : normal0_000 = staged_normal0_000 := by
  have h : mergeFuel 5000 staged_normal0_0000 staged_normal0_0001 = staged_normal0_000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_0000_staged normal0_0001_staged).trans h
#print axioms normal0_000_staged


def staged_normal0_0010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,false,true,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_0010_staged : normal0_0010 = staged_normal0_0010 := by
  have h : mergeFuel 5000 normal0_00100 normal0_00101 = staged_normal0_0010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_00100) (Eq.refl normal0_00101)).trans h
#print axioms normal0_0010_staged


def staged_normal0_0011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,false,true,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_0011_staged : normal0_0011 = staged_normal0_0011 := by
  have h : mergeFuel 5000 normal0_00110 normal0_00111 = staged_normal0_0011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_00110) (Eq.refl normal0_00111)).trans h
#print axioms normal0_0011_staged


def staged_normal0_001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,false,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_001_staged : normal0_001 = staged_normal0_001 := by
  have h : mergeFuel 5000 staged_normal0_0010 staged_normal0_0011 = staged_normal0_001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_0010_staged normal0_0011_staged).trans h
#print axioms normal0_001_staged


def staged_normal0_00 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_00_staged : normal0_00 = staged_normal0_00 := by
  have h : mergeFuel 5000 staged_normal0_000 staged_normal0_001 = staged_normal0_00 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_000_staged normal0_001_staged).trans h
#print axioms normal0_00_staged


def staged_normal0_0100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,true,false,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_0100_staged : normal0_0100 = staged_normal0_0100 := by
  have h : mergeFuel 5000 normal0_01000 normal0_01001 = staged_normal0_0100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_01000) (Eq.refl normal0_01001)).trans h
#print axioms normal0_0100_staged


def staged_normal0_0101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,true,false,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_0101_staged : normal0_0101 = staged_normal0_0101 := by
  have h : mergeFuel 5000 normal0_01010 normal0_01011 = staged_normal0_0101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_01010) (Eq.refl normal0_01011)).trans h
#print axioms normal0_0101_staged


def staged_normal0_010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,true,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_010_staged : normal0_010 = staged_normal0_010 := by
  have h : mergeFuel 5000 staged_normal0_0100 staged_normal0_0101 = staged_normal0_010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_0100_staged normal0_0101_staged).trans h
#print axioms normal0_010_staged


def staged_normal0_0110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,true,true,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_0110_staged : normal0_0110 = staged_normal0_0110 := by
  have h : mergeFuel 5000 normal0_01100 normal0_01101 = staged_normal0_0110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_01100) (Eq.refl normal0_01101)).trans h
#print axioms normal0_0110_staged


def staged_normal0_0111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,true,true,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_0111_staged : normal0_0111 = staged_normal0_0111 := by
  have h : mergeFuel 5000 normal0_01110 normal0_01111 = staged_normal0_0111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_01110) (Eq.refl normal0_01111)).trans h
#print axioms normal0_0111_staged


def staged_normal0_011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,true,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_011_staged : normal0_011 = staged_normal0_011 := by
  have h : mergeFuel 5000 staged_normal0_0110 staged_normal0_0111 = staged_normal0_011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_0110_staged normal0_0111_staged).trans h
#print axioms normal0_011_staged


def staged_normal0_01 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_01_staged : normal0_01 = staged_normal0_01 := by
  have h : mergeFuel 5000 staged_normal0_010 staged_normal0_011 = staged_normal0_01 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_010_staged normal0_011_staged).trans h
#print axioms normal0_01_staged


def staged_normal0_0 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_0_staged : normal0_0 = staged_normal0_0 := by
  have h : mergeFuel 5000 staged_normal0_00 staged_normal0_01 = staged_normal0_0 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_00_staged normal0_01_staged).trans h
#print axioms normal0_0_staged


def staged_normal0_1000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,false,false,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_1000_staged : normal0_1000 = staged_normal0_1000 := by
  have h : mergeFuel 5000 normal0_10000 normal0_10001 = staged_normal0_1000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_10000) (Eq.refl normal0_10001)).trans h
#print axioms normal0_1000_staged


def staged_normal0_1001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,false,false,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_1001_staged : normal0_1001 = staged_normal0_1001 := by
  have h : mergeFuel 5000 normal0_10010 normal0_10011 = staged_normal0_1001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_10010) (Eq.refl normal0_10011)).trans h
#print axioms normal0_1001_staged


def staged_normal0_100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,false,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_100_staged : normal0_100 = staged_normal0_100 := by
  have h : mergeFuel 5000 staged_normal0_1000 staged_normal0_1001 = staged_normal0_100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_1000_staged normal0_1001_staged).trans h
#print axioms normal0_100_staged


def staged_normal0_1010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,false,true,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_1010_staged : normal0_1010 = staged_normal0_1010 := by
  have h : mergeFuel 5000 normal0_10100 normal0_10101 = staged_normal0_1010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_10100) (Eq.refl normal0_10101)).trans h
#print axioms normal0_1010_staged


def staged_normal0_1011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,false,true,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_1011_staged : normal0_1011 = staged_normal0_1011 := by
  have h : mergeFuel 5000 normal0_10110 normal0_10111 = staged_normal0_1011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_10110) (Eq.refl normal0_10111)).trans h
#print axioms normal0_1011_staged


def staged_normal0_101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,false,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_101_staged : normal0_101 = staged_normal0_101 := by
  have h : mergeFuel 5000 staged_normal0_1010 staged_normal0_1011 = staged_normal0_101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_1010_staged normal0_1011_staged).trans h
#print axioms normal0_101_staged


def staged_normal0_10 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_10_staged : normal0_10 = staged_normal0_10 := by
  have h : mergeFuel 5000 staged_normal0_100 staged_normal0_101 = staged_normal0_10 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_100_staged normal0_101_staged).trans h
#print axioms normal0_10_staged


def staged_normal0_1100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,true,false,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_1100_staged : normal0_1100 = staged_normal0_1100 := by
  have h : mergeFuel 5000 normal0_11000 normal0_11001 = staged_normal0_1100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_11000) (Eq.refl normal0_11001)).trans h
#print axioms normal0_1100_staged


def staged_normal0_1101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,true,false,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_1101_staged : normal0_1101 = staged_normal0_1101 := by
  have h : mergeFuel 5000 normal0_11010 normal0_11011 = staged_normal0_1101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_11010) (Eq.refl normal0_11011)).trans h
#print axioms normal0_1101_staged


def staged_normal0_110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,true,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_110_staged : normal0_110 = staged_normal0_110 := by
  have h : mergeFuel 5000 staged_normal0_1100 staged_normal0_1101 = staged_normal0_110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_1100_staged normal0_1101_staged).trans h
#print axioms normal0_110_staged


def staged_normal0_1110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,true,true,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_1110_staged : normal0_1110 = staged_normal0_1110 := by
  have h : mergeFuel 5000 normal0_11100 normal0_11101 = staged_normal0_1110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_11100) (Eq.refl normal0_11101)).trans h
#print axioms normal0_1110_staged


def staged_normal0_1111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,true,true,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_1111_staged : normal0_1111 = staged_normal0_1111 := by
  have h : mergeFuel 5000 normal0_11110 normal0_11111 = staged_normal0_1111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_11110) (Eq.refl normal0_11111)).trans h
#print axioms normal0_1111_staged


def staged_normal0_111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,true,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_111_staged : normal0_111 = staged_normal0_111 := by
  have h : mergeFuel 5000 staged_normal0_1110 staged_normal0_1111 = staged_normal0_111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_1110_staged normal0_1111_staged).trans h
#print axioms normal0_111_staged


def staged_normal0_11 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true,true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_11_staged : normal0_11 = staged_normal0_11 := by
  have h : mergeFuel 5000 staged_normal0_110 staged_normal0_111 = staged_normal0_11 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_110_staged normal0_111_staged).trans h
#print axioms normal0_11_staged


def staged_normal0_1 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [true] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_1_staged : normal0_1 = staged_normal0_1 := by
  have h : mergeFuel 5000 staged_normal0_10 staged_normal0_11 = staged_normal0_1 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_10_staged normal0_11_staged).trans h
#print axioms normal0_1_staged


def staged_normal0_root : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate0)
theorem normal0_root_staged : normal0_root = staged_normal0_root := by
  have h : mergeFuel 5000 staged_normal0_0 staged_normal0_1 = staged_normal0_root := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_0_staged normal0_1_staged).trans h
#print axioms normal0_root_staged


def staged_normal1_0000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.inputs
  (descend [false,false,false,false] QuantitativeArithmeticSmallLevelNineteenFinalCertificateCompute.certificate1)
theorem normal1_0000_staged : normal1_0000 = staged_normal1_0000 := by
  have h : mergeFuel 5000 normal1_00000 normal1_00001 = staged_normal1_0000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_00000) (Eq.refl normal1_00001)).trans h
#print axioms normal1_0000_staged

}
end QuantitativeArithmeticSmallLevelNineteenFinalCertificate
end

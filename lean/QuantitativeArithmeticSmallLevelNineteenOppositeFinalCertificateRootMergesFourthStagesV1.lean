module
public import QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateRootMergesThirdStagesV1
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
def staged_normal0_111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_111_staged : normal0_111 = staged_normal0_111 := by
  have h : mergeFuel 5000 staged_normal0_1110 staged_normal0_1111 = staged_normal0_111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_1110_staged normal0_1111_staged).trans h
#print axioms normal0_111_staged


def staged_normal0_11 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_11_staged : normal0_11 = staged_normal0_11 := by
  have h : mergeFuel 5000 staged_normal0_110 staged_normal0_111 = staged_normal0_11 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_110_staged normal0_111_staged).trans h
#print axioms normal0_11_staged


def staged_normal0_1 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1_staged : normal0_1 = staged_normal0_1 := by
  have h : mergeFuel 5000 staged_normal0_10 staged_normal0_11 = staged_normal0_1 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_10_staged normal0_11_staged).trans h
#print axioms normal0_1_staged


def staged_normal0_root : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_root_staged : normal0_root = staged_normal0_root := by
  have h : mergeFuel 5000 staged_normal0_0 staged_normal0_1 = staged_normal0_root := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_0_staged normal0_1_staged).trans h
#print axioms normal0_root_staged


def staged_normal1_00000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_00000_staged : normal1_00000 = staged_normal1_00000 := by
  have h : mergeFuel 5000 normal1_000000 normal1_000001 = staged_normal1_00000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_000000) (Eq.refl normal1_000001)).trans h
#print axioms normal1_00000_staged


def staged_normal1_00001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_00001_staged : normal1_00001 = staged_normal1_00001 := by
  have h : mergeFuel 5000 normal1_000010 normal1_000011 = staged_normal1_00001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_000010) (Eq.refl normal1_000011)).trans h
#print axioms normal1_00001_staged


def staged_normal1_0000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_0000_staged : normal1_0000 = staged_normal1_0000 := by
  have h : mergeFuel 5000 staged_normal1_00000 staged_normal1_00001 = staged_normal1_0000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_00000_staged normal1_00001_staged).trans h
#print axioms normal1_0000_staged


def staged_normal1_00010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_00010_staged : normal1_00010 = staged_normal1_00010 := by
  have h : mergeFuel 5000 normal1_000100 normal1_000101 = staged_normal1_00010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_000100) (Eq.refl normal1_000101)).trans h
#print axioms normal1_00010_staged


def staged_normal1_00011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_00011_staged : normal1_00011 = staged_normal1_00011 := by
  have h : mergeFuel 5000 normal1_000110 normal1_000111 = staged_normal1_00011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_000110) (Eq.refl normal1_000111)).trans h
#print axioms normal1_00011_staged


def staged_normal1_0001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_0001_staged : normal1_0001 = staged_normal1_0001 := by
  have h : mergeFuel 5000 staged_normal1_00010 staged_normal1_00011 = staged_normal1_0001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_00010_staged normal1_00011_staged).trans h
#print axioms normal1_0001_staged


def staged_normal1_000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_000_staged : normal1_000 = staged_normal1_000 := by
  have h : mergeFuel 5000 staged_normal1_0000 staged_normal1_0001 = staged_normal1_000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_0000_staged normal1_0001_staged).trans h
#print axioms normal1_000_staged


def staged_normal1_00100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_00100_staged : normal1_00100 = staged_normal1_00100 := by
  have h : mergeFuel 5000 normal1_001000 normal1_001001 = staged_normal1_00100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_001000) (Eq.refl normal1_001001)).trans h
#print axioms normal1_00100_staged


def staged_normal1_00101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_00101_staged : normal1_00101 = staged_normal1_00101 := by
  have h : mergeFuel 5000 normal1_001010 normal1_001011 = staged_normal1_00101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_001010) (Eq.refl normal1_001011)).trans h
#print axioms normal1_00101_staged


def staged_normal1_0010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_0010_staged : normal1_0010 = staged_normal1_0010 := by
  have h : mergeFuel 5000 staged_normal1_00100 staged_normal1_00101 = staged_normal1_0010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_00100_staged normal1_00101_staged).trans h
#print axioms normal1_0010_staged


def staged_normal1_00110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_00110_staged : normal1_00110 = staged_normal1_00110 := by
  have h : mergeFuel 5000 normal1_001100 normal1_001101 = staged_normal1_00110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_001100) (Eq.refl normal1_001101)).trans h
#print axioms normal1_00110_staged


def staged_normal1_00111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_00111_staged : normal1_00111 = staged_normal1_00111 := by
  have h : mergeFuel 5000 normal1_001110 normal1_001111 = staged_normal1_00111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_001110) (Eq.refl normal1_001111)).trans h
#print axioms normal1_00111_staged


def staged_normal1_0011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_0011_staged : normal1_0011 = staged_normal1_0011 := by
  have h : mergeFuel 5000 staged_normal1_00110 staged_normal1_00111 = staged_normal1_0011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_00110_staged normal1_00111_staged).trans h
#print axioms normal1_0011_staged


def staged_normal1_001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_001_staged : normal1_001 = staged_normal1_001 := by
  have h : mergeFuel 5000 staged_normal1_0010 staged_normal1_0011 = staged_normal1_001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_0010_staged normal1_0011_staged).trans h
#print axioms normal1_001_staged


def staged_normal1_00 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_00_staged : normal1_00 = staged_normal1_00 := by
  have h : mergeFuel 5000 staged_normal1_000 staged_normal1_001 = staged_normal1_00 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_000_staged normal1_001_staged).trans h
#print axioms normal1_00_staged


def staged_normal1_01000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_01000_staged : normal1_01000 = staged_normal1_01000 := by
  have h : mergeFuel 5000 normal1_010000 normal1_010001 = staged_normal1_01000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_010000) (Eq.refl normal1_010001)).trans h
#print axioms normal1_01000_staged


def staged_normal1_01001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_01001_staged : normal1_01001 = staged_normal1_01001 := by
  have h : mergeFuel 5000 normal1_010010 normal1_010011 = staged_normal1_01001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_010010) (Eq.refl normal1_010011)).trans h
#print axioms normal1_01001_staged


def staged_normal1_0100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_0100_staged : normal1_0100 = staged_normal1_0100 := by
  have h : mergeFuel 5000 staged_normal1_01000 staged_normal1_01001 = staged_normal1_0100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_01000_staged normal1_01001_staged).trans h
#print axioms normal1_0100_staged


def staged_normal1_010101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_010101_staged : normal1_010101 = staged_normal1_010101 := by
  have h : mergeFuel 5000 normal1_0101010 normal1_0101011 = staged_normal1_010101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_0101010) (Eq.refl normal1_0101011)).trans h
#print axioms normal1_010101_staged


def staged_normal1_01010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_01010_staged : normal1_01010 = staged_normal1_01010 := by
  have h : mergeFuel 5000 normal1_010100 staged_normal1_010101 = staged_normal1_01010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_010100) normal1_010101_staged).trans h
#print axioms normal1_01010_staged


def staged_normal1_010110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_010110_staged : normal1_010110 = staged_normal1_010110 := by
  have h : mergeFuel 5000 normal1_0101100 normal1_0101101 = staged_normal1_010110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_0101100) (Eq.refl normal1_0101101)).trans h
#print axioms normal1_010110_staged


def staged_normal1_010111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_010111_staged : normal1_010111 = staged_normal1_010111 := by
  have h : mergeFuel 5000 normal1_0101110 normal1_0101111 = staged_normal1_010111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_0101110) (Eq.refl normal1_0101111)).trans h
#print axioms normal1_010111_staged


def staged_normal1_01011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_01011_staged : normal1_01011 = staged_normal1_01011 := by
  have h : mergeFuel 5000 staged_normal1_010110 staged_normal1_010111 = staged_normal1_01011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_010110_staged normal1_010111_staged).trans h
#print axioms normal1_01011_staged


def staged_normal1_0101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_0101_staged : normal1_0101 = staged_normal1_0101 := by
  have h : mergeFuel 5000 staged_normal1_01010 staged_normal1_01011 = staged_normal1_0101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_01010_staged normal1_01011_staged).trans h
#print axioms normal1_0101_staged


def staged_normal1_010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_010_staged : normal1_010 = staged_normal1_010 := by
  have h : mergeFuel 5000 staged_normal1_0100 staged_normal1_0101 = staged_normal1_010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_0100_staged normal1_0101_staged).trans h
#print axioms normal1_010_staged


def staged_normal1_011000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_011000_staged : normal1_011000 = staged_normal1_011000 := by
  have h : mergeFuel 5000 normal1_0110000 normal1_0110001 = staged_normal1_011000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_0110000) (Eq.refl normal1_0110001)).trans h
#print axioms normal1_011000_staged


def staged_normal1_011001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_011001_staged : normal1_011001 = staged_normal1_011001 := by
  have h : mergeFuel 5000 normal1_0110010 normal1_0110011 = staged_normal1_011001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_0110010) (Eq.refl normal1_0110011)).trans h
#print axioms normal1_011001_staged


def staged_normal1_01100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_01100_staged : normal1_01100 = staged_normal1_01100 := by
  have h : mergeFuel 5000 staged_normal1_011000 staged_normal1_011001 = staged_normal1_01100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_011000_staged normal1_011001_staged).trans h
#print axioms normal1_01100_staged

}
end QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificate
end

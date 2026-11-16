module
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
def staged_normal0_00000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_00000_staged : normal0_00000 = staged_normal0_00000 := by
  have h : mergeFuel 5000 normal0_000000 normal0_000001 = staged_normal0_00000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_000000) (Eq.refl normal0_000001)).trans h
#print axioms normal0_00000_staged


def staged_normal0_00001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_00001_staged : normal0_00001 = staged_normal0_00001 := by
  have h : mergeFuel 5000 normal0_000010 normal0_000011 = staged_normal0_00001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_000010) (Eq.refl normal0_000011)).trans h
#print axioms normal0_00001_staged


def staged_normal0_0000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_0000_staged : normal0_0000 = staged_normal0_0000 := by
  have h : mergeFuel 5000 staged_normal0_00000 staged_normal0_00001 = staged_normal0_0000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_00000_staged normal0_00001_staged).trans h
#print axioms normal0_0000_staged


def staged_normal0_00010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_00010_staged : normal0_00010 = staged_normal0_00010 := by
  have h : mergeFuel 5000 normal0_000100 normal0_000101 = staged_normal0_00010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_000100) (Eq.refl normal0_000101)).trans h
#print axioms normal0_00010_staged


def staged_normal0_00011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_00011_staged : normal0_00011 = staged_normal0_00011 := by
  have h : mergeFuel 5000 normal0_000110 normal0_000111 = staged_normal0_00011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_000110) (Eq.refl normal0_000111)).trans h
#print axioms normal0_00011_staged


def staged_normal0_0001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_0001_staged : normal0_0001 = staged_normal0_0001 := by
  have h : mergeFuel 5000 staged_normal0_00010 staged_normal0_00011 = staged_normal0_0001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_00010_staged normal0_00011_staged).trans h
#print axioms normal0_0001_staged


def staged_normal0_000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_000_staged : normal0_000 = staged_normal0_000 := by
  have h : mergeFuel 5000 staged_normal0_0000 staged_normal0_0001 = staged_normal0_000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_0000_staged normal0_0001_staged).trans h
#print axioms normal0_000_staged


def staged_normal0_00100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_00100_staged : normal0_00100 = staged_normal0_00100 := by
  have h : mergeFuel 5000 normal0_001000 normal0_001001 = staged_normal0_00100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_001000) (Eq.refl normal0_001001)).trans h
#print axioms normal0_00100_staged


def staged_normal0_00101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_00101_staged : normal0_00101 = staged_normal0_00101 := by
  have h : mergeFuel 5000 normal0_001010 normal0_001011 = staged_normal0_00101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_001010) (Eq.refl normal0_001011)).trans h
#print axioms normal0_00101_staged


def staged_normal0_0010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_0010_staged : normal0_0010 = staged_normal0_0010 := by
  have h : mergeFuel 5000 staged_normal0_00100 staged_normal0_00101 = staged_normal0_0010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_00100_staged normal0_00101_staged).trans h
#print axioms normal0_0010_staged


def staged_normal0_00110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_00110_staged : normal0_00110 = staged_normal0_00110 := by
  have h : mergeFuel 5000 normal0_001100 normal0_001101 = staged_normal0_00110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_001100) (Eq.refl normal0_001101)).trans h
#print axioms normal0_00110_staged


def staged_normal0_00111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_00111_staged : normal0_00111 = staged_normal0_00111 := by
  have h : mergeFuel 5000 normal0_001110 normal0_001111 = staged_normal0_00111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_001110) (Eq.refl normal0_001111)).trans h
#print axioms normal0_00111_staged


def staged_normal0_0011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_0011_staged : normal0_0011 = staged_normal0_0011 := by
  have h : mergeFuel 5000 staged_normal0_00110 staged_normal0_00111 = staged_normal0_0011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_00110_staged normal0_00111_staged).trans h
#print axioms normal0_0011_staged


def staged_normal0_001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_001_staged : normal0_001 = staged_normal0_001 := by
  have h : mergeFuel 5000 staged_normal0_0010 staged_normal0_0011 = staged_normal0_001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_0010_staged normal0_0011_staged).trans h
#print axioms normal0_001_staged


def staged_normal0_00 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_00_staged : normal0_00 = staged_normal0_00 := by
  have h : mergeFuel 5000 staged_normal0_000 staged_normal0_001 = staged_normal0_00 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_000_staged normal0_001_staged).trans h
#print axioms normal0_00_staged


def staged_normal0_01000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_01000_staged : normal0_01000 = staged_normal0_01000 := by
  have h : mergeFuel 5000 normal0_010000 normal0_010001 = staged_normal0_01000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_010000) (Eq.refl normal0_010001)).trans h
#print axioms normal0_01000_staged


def staged_normal0_01001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_01001_staged : normal0_01001 = staged_normal0_01001 := by
  have h : mergeFuel 5000 normal0_010010 normal0_010011 = staged_normal0_01001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_010010) (Eq.refl normal0_010011)).trans h
#print axioms normal0_01001_staged


def staged_normal0_0100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_0100_staged : normal0_0100 = staged_normal0_0100 := by
  have h : mergeFuel 5000 staged_normal0_01000 staged_normal0_01001 = staged_normal0_0100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_01000_staged normal0_01001_staged).trans h
#print axioms normal0_0100_staged


def staged_normal0_010101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_010101_staged : normal0_010101 = staged_normal0_010101 := by
  have h : mergeFuel 5000 normal0_0101010 normal0_0101011 = staged_normal0_010101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_0101010) (Eq.refl normal0_0101011)).trans h
#print axioms normal0_010101_staged


def staged_normal0_01010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_01010_staged : normal0_01010 = staged_normal0_01010 := by
  have h : mergeFuel 5000 normal0_010100 staged_normal0_010101 = staged_normal0_01010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_010100) normal0_010101_staged).trans h
#print axioms normal0_01010_staged


def staged_normal0_010110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_010110_staged : normal0_010110 = staged_normal0_010110 := by
  have h : mergeFuel 5000 normal0_0101100 normal0_0101101 = staged_normal0_010110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_0101100) (Eq.refl normal0_0101101)).trans h
#print axioms normal0_010110_staged


def staged_normal0_010111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_010111_staged : normal0_010111 = staged_normal0_010111 := by
  have h : mergeFuel 5000 normal0_0101110 normal0_0101111 = staged_normal0_010111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_0101110) (Eq.refl normal0_0101111)).trans h
#print axioms normal0_010111_staged


def staged_normal0_01011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_01011_staged : normal0_01011 = staged_normal0_01011 := by
  have h : mergeFuel 5000 staged_normal0_010110 staged_normal0_010111 = staged_normal0_01011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_010110_staged normal0_010111_staged).trans h
#print axioms normal0_01011_staged


def staged_normal0_0101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_0101_staged : normal0_0101 = staged_normal0_0101 := by
  have h : mergeFuel 5000 staged_normal0_01010 staged_normal0_01011 = staged_normal0_0101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_01010_staged normal0_01011_staged).trans h
#print axioms normal0_0101_staged


def staged_normal0_010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_010_staged : normal0_010 = staged_normal0_010 := by
  have h : mergeFuel 5000 staged_normal0_0100 staged_normal0_0101 = staged_normal0_010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_0100_staged normal0_0101_staged).trans h
#print axioms normal0_010_staged


def staged_normal0_011000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_011000_staged : normal0_011000 = staged_normal0_011000 := by
  have h : mergeFuel 5000 normal0_0110000 normal0_0110001 = staged_normal0_011000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_0110000) (Eq.refl normal0_0110001)).trans h
#print axioms normal0_011000_staged


def staged_normal0_011001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_011001_staged : normal0_011001 = staged_normal0_011001 := by
  have h : mergeFuel 5000 normal0_0110010 normal0_0110011 = staged_normal0_011001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_0110010) (Eq.refl normal0_0110011)).trans h
#print axioms normal0_011001_staged


def staged_normal0_01100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_01100_staged : normal0_01100 = staged_normal0_01100 := by
  have h : mergeFuel 5000 staged_normal0_011000 staged_normal0_011001 = staged_normal0_01100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_011000_staged normal0_011001_staged).trans h
#print axioms normal0_01100_staged


def staged_normal0_011010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_011010_staged : normal0_011010 = staged_normal0_011010 := by
  have h : mergeFuel 5000 normal0_0110100 normal0_0110101 = staged_normal0_011010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_0110100) (Eq.refl normal0_0110101)).trans h
#print axioms normal0_011010_staged


def staged_normal0_011011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_011011_staged : normal0_011011 = staged_normal0_011011 := by
  have h : mergeFuel 5000 normal0_0110110 normal0_0110111 = staged_normal0_011011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_0110110) (Eq.refl normal0_0110111)).trans h
#print axioms normal0_011011_staged


def staged_normal0_01101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_01101_staged : normal0_01101 = staged_normal0_01101 := by
  have h : mergeFuel 5000 staged_normal0_011010 staged_normal0_011011 = staged_normal0_01101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_011010_staged normal0_011011_staged).trans h
#print axioms normal0_01101_staged


def staged_normal0_0110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_0110_staged : normal0_0110 = staged_normal0_0110 := by
  have h : mergeFuel 5000 staged_normal0_01100 staged_normal0_01101 = staged_normal0_0110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_01100_staged normal0_01101_staged).trans h
#print axioms normal0_0110_staged

}
end QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificate
end

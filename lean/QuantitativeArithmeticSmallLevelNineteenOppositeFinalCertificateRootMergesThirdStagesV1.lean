module
public import QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateRootMergesSecondStagesV1
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
def staged_normal0_1101000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1101000_staged : normal0_1101000 = staged_normal0_1101000 := by
  have h : mergeFuel 5000 normal0_11010000 normal0_11010001 = staged_normal0_1101000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_11010000) (Eq.refl normal0_11010001)).trans h
#print axioms normal0_1101000_staged


def staged_normal0_1101001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1101001_staged : normal0_1101001 = staged_normal0_1101001 := by
  have h : mergeFuel 5000 normal0_11010010 normal0_11010011 = staged_normal0_1101001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_11010010) (Eq.refl normal0_11010011)).trans h
#print axioms normal0_1101001_staged


def staged_normal0_110100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_110100_staged : normal0_110100 = staged_normal0_110100 := by
  have h : mergeFuel 5000 staged_normal0_1101000 staged_normal0_1101001 = staged_normal0_110100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_1101000_staged normal0_1101001_staged).trans h
#print axioms normal0_110100_staged


def staged_normal0_1101010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1101010_staged : normal0_1101010 = staged_normal0_1101010 := by
  have h : mergeFuel 5000 normal0_11010100 normal0_11010101 = staged_normal0_1101010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_11010100) (Eq.refl normal0_11010101)).trans h
#print axioms normal0_1101010_staged


def staged_normal0_1101011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1101011_staged : normal0_1101011 = staged_normal0_1101011 := by
  have h : mergeFuel 5000 normal0_11010110 normal0_11010111 = staged_normal0_1101011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_11010110) (Eq.refl normal0_11010111)).trans h
#print axioms normal0_1101011_staged


def staged_normal0_110101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_110101_staged : normal0_110101 = staged_normal0_110101 := by
  have h : mergeFuel 5000 staged_normal0_1101010 staged_normal0_1101011 = staged_normal0_110101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_1101010_staged normal0_1101011_staged).trans h
#print axioms normal0_110101_staged


def staged_normal0_11010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_11010_staged : normal0_11010 = staged_normal0_11010 := by
  have h : mergeFuel 5000 staged_normal0_110100 staged_normal0_110101 = staged_normal0_11010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_110100_staged normal0_110101_staged).trans h
#print axioms normal0_11010_staged


def staged_normal0_1101100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1101100_staged : normal0_1101100 = staged_normal0_1101100 := by
  have h : mergeFuel 5000 normal0_11011000 normal0_11011001 = staged_normal0_1101100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_11011000) (Eq.refl normal0_11011001)).trans h
#print axioms normal0_1101100_staged


def staged_normal0_1101101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1101101_staged : normal0_1101101 = staged_normal0_1101101 := by
  have h : mergeFuel 5000 normal0_11011010 normal0_11011011 = staged_normal0_1101101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_11011010) (Eq.refl normal0_11011011)).trans h
#print axioms normal0_1101101_staged


def staged_normal0_110110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_110110_staged : normal0_110110 = staged_normal0_110110 := by
  have h : mergeFuel 5000 staged_normal0_1101100 staged_normal0_1101101 = staged_normal0_110110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_1101100_staged normal0_1101101_staged).trans h
#print axioms normal0_110110_staged


def staged_normal0_1101110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1101110_staged : normal0_1101110 = staged_normal0_1101110 := by
  have h : mergeFuel 5000 normal0_11011100 normal0_11011101 = staged_normal0_1101110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_11011100) (Eq.refl normal0_11011101)).trans h
#print axioms normal0_1101110_staged


def staged_normal0_11011111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,true,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_11011111_staged : normal0_11011111 = staged_normal0_11011111 := by
  have h : mergeFuel 5000 normal0_110111110 normal0_110111111 = staged_normal0_11011111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_110111110) (Eq.refl normal0_110111111)).trans h
#print axioms normal0_11011111_staged


def staged_normal0_1101111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1101111_staged : normal0_1101111 = staged_normal0_1101111 := by
  have h : mergeFuel 5000 normal0_11011110 staged_normal0_11011111 = staged_normal0_1101111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_11011110) normal0_11011111_staged).trans h
#print axioms normal0_1101111_staged


def staged_normal0_110111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_110111_staged : normal0_110111 = staged_normal0_110111 := by
  have h : mergeFuel 5000 staged_normal0_1101110 staged_normal0_1101111 = staged_normal0_110111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_1101110_staged normal0_1101111_staged).trans h
#print axioms normal0_110111_staged


def staged_normal0_11011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_11011_staged : normal0_11011 = staged_normal0_11011 := by
  have h : mergeFuel 5000 staged_normal0_110110 staged_normal0_110111 = staged_normal0_11011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_110110_staged normal0_110111_staged).trans h
#print axioms normal0_11011_staged


def staged_normal0_1101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1101_staged : normal0_1101 = staged_normal0_1101 := by
  have h : mergeFuel 5000 staged_normal0_11010 staged_normal0_11011 = staged_normal0_1101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_11010_staged normal0_11011_staged).trans h
#print axioms normal0_1101_staged


def staged_normal0_110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_110_staged : normal0_110 = staged_normal0_110 := by
  have h : mergeFuel 5000 staged_normal0_1100 staged_normal0_1101 = staged_normal0_110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_1100_staged normal0_1101_staged).trans h
#print axioms normal0_110_staged


def staged_normal0_1110000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,false,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1110000_staged : normal0_1110000 = staged_normal0_1110000 := by
  have h : mergeFuel 5000 normal0_11100000 normal0_11100001 = staged_normal0_1110000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_11100000) (Eq.refl normal0_11100001)).trans h
#print axioms normal0_1110000_staged


def staged_normal0_111000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_111000_staged : normal0_111000 = staged_normal0_111000 := by
  have h : mergeFuel 5000 staged_normal0_1110000 normal0_1110001 = staged_normal0_111000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_1110000_staged (Eq.refl normal0_1110001)).trans h
#print axioms normal0_111000_staged


def staged_normal0_111001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_111001_staged : normal0_111001 = staged_normal0_111001 := by
  have h : mergeFuel 5000 normal0_1110010 normal0_1110011 = staged_normal0_111001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_1110010) (Eq.refl normal0_1110011)).trans h
#print axioms normal0_111001_staged


def staged_normal0_11100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_11100_staged : normal0_11100 = staged_normal0_11100 := by
  have h : mergeFuel 5000 staged_normal0_111000 staged_normal0_111001 = staged_normal0_11100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_111000_staged normal0_111001_staged).trans h
#print axioms normal0_11100_staged


def staged_normal0_111010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_111010_staged : normal0_111010 = staged_normal0_111010 := by
  have h : mergeFuel 5000 normal0_1110100 normal0_1110101 = staged_normal0_111010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_1110100) (Eq.refl normal0_1110101)).trans h
#print axioms normal0_111010_staged


def staged_normal0_111011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_111011_staged : normal0_111011 = staged_normal0_111011 := by
  have h : mergeFuel 5000 normal0_1110110 normal0_1110111 = staged_normal0_111011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_1110110) (Eq.refl normal0_1110111)).trans h
#print axioms normal0_111011_staged


def staged_normal0_11101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_11101_staged : normal0_11101 = staged_normal0_11101 := by
  have h : mergeFuel 5000 staged_normal0_111010 staged_normal0_111011 = staged_normal0_11101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_111010_staged normal0_111011_staged).trans h
#print axioms normal0_11101_staged


def staged_normal0_1110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1110_staged : normal0_1110 = staged_normal0_1110 := by
  have h : mergeFuel 5000 staged_normal0_11100 staged_normal0_11101 = staged_normal0_1110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_11100_staged normal0_11101_staged).trans h
#print axioms normal0_1110_staged


def staged_normal0_111100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_111100_staged : normal0_111100 = staged_normal0_111100 := by
  have h : mergeFuel 5000 normal0_1111000 normal0_1111001 = staged_normal0_111100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_1111000) (Eq.refl normal0_1111001)).trans h
#print axioms normal0_111100_staged


def staged_normal0_111101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_111101_staged : normal0_111101 = staged_normal0_111101 := by
  have h : mergeFuel 5000 normal0_1111010 normal0_1111011 = staged_normal0_111101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_1111010) (Eq.refl normal0_1111011)).trans h
#print axioms normal0_111101_staged


def staged_normal0_11110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_11110_staged : normal0_11110 = staged_normal0_11110 := by
  have h : mergeFuel 5000 staged_normal0_111100 staged_normal0_111101 = staged_normal0_11110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_111100_staged normal0_111101_staged).trans h
#print axioms normal0_11110_staged


def staged_normal0_111110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_111110_staged : normal0_111110 = staged_normal0_111110 := by
  have h : mergeFuel 5000 normal0_1111100 normal0_1111101 = staged_normal0_111110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_1111100) (Eq.refl normal0_1111101)).trans h
#print axioms normal0_111110_staged


def staged_normal0_111111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_111111_staged : normal0_111111 = staged_normal0_111111 := by
  have h : mergeFuel 5000 normal0_1111110 normal0_1111111 = staged_normal0_111111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_1111110) (Eq.refl normal0_1111111)).trans h
#print axioms normal0_111111_staged


def staged_normal0_11111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_11111_staged : normal0_11111 = staged_normal0_11111 := by
  have h : mergeFuel 5000 staged_normal0_111110 staged_normal0_111111 = staged_normal0_11111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_111110_staged normal0_111111_staged).trans h
#print axioms normal0_11111_staged


def staged_normal0_1111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1111_staged : normal0_1111 = staged_normal0_1111 := by
  have h : mergeFuel 5000 staged_normal0_11110 staged_normal0_11111 = staged_normal0_1111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_11110_staged normal0_11111_staged).trans h
#print axioms normal0_1111_staged

}
end QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificate
end

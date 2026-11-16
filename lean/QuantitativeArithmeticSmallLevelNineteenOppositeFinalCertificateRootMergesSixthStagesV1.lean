module
public import QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateRootMergesFifthStagesV1
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
def staged_normal1_1100111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,false,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1100111_staged : normal1_1100111 = staged_normal1_1100111 := by
  have h : mergeFuel 5000 normal1_11001110 staged_normal1_11001111 = staged_normal1_1100111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_11001110) normal1_11001111_staged).trans h
#print axioms normal1_1100111_staged


def staged_normal1_110011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_110011_staged : normal1_110011 = staged_normal1_110011 := by
  have h : mergeFuel 5000 normal1_1100110 staged_normal1_1100111 = staged_normal1_110011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_1100110) normal1_1100111_staged).trans h
#print axioms normal1_110011_staged


def staged_normal1_11001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_11001_staged : normal1_11001 = staged_normal1_11001 := by
  have h : mergeFuel 5000 normal1_110010 staged_normal1_110011 = staged_normal1_11001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_110010) normal1_110011_staged).trans h
#print axioms normal1_11001_staged


def staged_normal1_1100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1100_staged : normal1_1100 = staged_normal1_1100 := by
  have h : mergeFuel 5000 staged_normal1_11000 staged_normal1_11001 = staged_normal1_1100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_11000_staged normal1_11001_staged).trans h
#print axioms normal1_1100_staged


def staged_normal1_1101000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1101000_staged : normal1_1101000 = staged_normal1_1101000 := by
  have h : mergeFuel 5000 normal1_11010000 normal1_11010001 = staged_normal1_1101000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_11010000) (Eq.refl normal1_11010001)).trans h
#print axioms normal1_1101000_staged


def staged_normal1_1101001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1101001_staged : normal1_1101001 = staged_normal1_1101001 := by
  have h : mergeFuel 5000 normal1_11010010 normal1_11010011 = staged_normal1_1101001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_11010010) (Eq.refl normal1_11010011)).trans h
#print axioms normal1_1101001_staged


def staged_normal1_110100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_110100_staged : normal1_110100 = staged_normal1_110100 := by
  have h : mergeFuel 5000 staged_normal1_1101000 staged_normal1_1101001 = staged_normal1_110100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_1101000_staged normal1_1101001_staged).trans h
#print axioms normal1_110100_staged


def staged_normal1_1101010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1101010_staged : normal1_1101010 = staged_normal1_1101010 := by
  have h : mergeFuel 5000 normal1_11010100 normal1_11010101 = staged_normal1_1101010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_11010100) (Eq.refl normal1_11010101)).trans h
#print axioms normal1_1101010_staged


def staged_normal1_1101011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1101011_staged : normal1_1101011 = staged_normal1_1101011 := by
  have h : mergeFuel 5000 normal1_11010110 normal1_11010111 = staged_normal1_1101011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_11010110) (Eq.refl normal1_11010111)).trans h
#print axioms normal1_1101011_staged


def staged_normal1_110101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_110101_staged : normal1_110101 = staged_normal1_110101 := by
  have h : mergeFuel 5000 staged_normal1_1101010 staged_normal1_1101011 = staged_normal1_110101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_1101010_staged normal1_1101011_staged).trans h
#print axioms normal1_110101_staged


def staged_normal1_11010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_11010_staged : normal1_11010 = staged_normal1_11010 := by
  have h : mergeFuel 5000 staged_normal1_110100 staged_normal1_110101 = staged_normal1_11010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_110100_staged normal1_110101_staged).trans h
#print axioms normal1_11010_staged


def staged_normal1_1101100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1101100_staged : normal1_1101100 = staged_normal1_1101100 := by
  have h : mergeFuel 5000 normal1_11011000 normal1_11011001 = staged_normal1_1101100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_11011000) (Eq.refl normal1_11011001)).trans h
#print axioms normal1_1101100_staged


def staged_normal1_1101101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1101101_staged : normal1_1101101 = staged_normal1_1101101 := by
  have h : mergeFuel 5000 normal1_11011010 normal1_11011011 = staged_normal1_1101101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_11011010) (Eq.refl normal1_11011011)).trans h
#print axioms normal1_1101101_staged


def staged_normal1_110110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_110110_staged : normal1_110110 = staged_normal1_110110 := by
  have h : mergeFuel 5000 staged_normal1_1101100 staged_normal1_1101101 = staged_normal1_110110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_1101100_staged normal1_1101101_staged).trans h
#print axioms normal1_110110_staged


def staged_normal1_1101110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1101110_staged : normal1_1101110 = staged_normal1_1101110 := by
  have h : mergeFuel 5000 normal1_11011100 normal1_11011101 = staged_normal1_1101110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_11011100) (Eq.refl normal1_11011101)).trans h
#print axioms normal1_1101110_staged


def staged_normal1_11011111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,true,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_11011111_staged : normal1_11011111 = staged_normal1_11011111 := by
  have h : mergeFuel 5000 normal1_110111110 normal1_110111111 = staged_normal1_11011111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_110111110) (Eq.refl normal1_110111111)).trans h
#print axioms normal1_11011111_staged


def staged_normal1_1101111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1101111_staged : normal1_1101111 = staged_normal1_1101111 := by
  have h : mergeFuel 5000 normal1_11011110 staged_normal1_11011111 = staged_normal1_1101111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_11011110) normal1_11011111_staged).trans h
#print axioms normal1_1101111_staged


def staged_normal1_110111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_110111_staged : normal1_110111 = staged_normal1_110111 := by
  have h : mergeFuel 5000 staged_normal1_1101110 staged_normal1_1101111 = staged_normal1_110111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_1101110_staged normal1_1101111_staged).trans h
#print axioms normal1_110111_staged


def staged_normal1_11011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_11011_staged : normal1_11011 = staged_normal1_11011 := by
  have h : mergeFuel 5000 staged_normal1_110110 staged_normal1_110111 = staged_normal1_11011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_110110_staged normal1_110111_staged).trans h
#print axioms normal1_11011_staged


def staged_normal1_1101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1101_staged : normal1_1101 = staged_normal1_1101 := by
  have h : mergeFuel 5000 staged_normal1_11010 staged_normal1_11011 = staged_normal1_1101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_11010_staged normal1_11011_staged).trans h
#print axioms normal1_1101_staged


def staged_normal1_110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_110_staged : normal1_110 = staged_normal1_110 := by
  have h : mergeFuel 5000 staged_normal1_1100 staged_normal1_1101 = staged_normal1_110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_1100_staged normal1_1101_staged).trans h
#print axioms normal1_110_staged


def staged_normal1_1110000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,false,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1110000_staged : normal1_1110000 = staged_normal1_1110000 := by
  have h : mergeFuel 5000 normal1_11100000 normal1_11100001 = staged_normal1_1110000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_11100000) (Eq.refl normal1_11100001)).trans h
#print axioms normal1_1110000_staged


def staged_normal1_111000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_111000_staged : normal1_111000 = staged_normal1_111000 := by
  have h : mergeFuel 5000 staged_normal1_1110000 normal1_1110001 = staged_normal1_111000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_1110000_staged (Eq.refl normal1_1110001)).trans h
#print axioms normal1_111000_staged


def staged_normal1_111001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_111001_staged : normal1_111001 = staged_normal1_111001 := by
  have h : mergeFuel 5000 normal1_1110010 normal1_1110011 = staged_normal1_111001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_1110010) (Eq.refl normal1_1110011)).trans h
#print axioms normal1_111001_staged


def staged_normal1_11100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_11100_staged : normal1_11100 = staged_normal1_11100 := by
  have h : mergeFuel 5000 staged_normal1_111000 staged_normal1_111001 = staged_normal1_11100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_111000_staged normal1_111001_staged).trans h
#print axioms normal1_11100_staged


def staged_normal1_111010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_111010_staged : normal1_111010 = staged_normal1_111010 := by
  have h : mergeFuel 5000 normal1_1110100 normal1_1110101 = staged_normal1_111010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_1110100) (Eq.refl normal1_1110101)).trans h
#print axioms normal1_111010_staged


def staged_normal1_111011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_111011_staged : normal1_111011 = staged_normal1_111011 := by
  have h : mergeFuel 5000 normal1_1110110 normal1_1110111 = staged_normal1_111011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_1110110) (Eq.refl normal1_1110111)).trans h
#print axioms normal1_111011_staged


def staged_normal1_11101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_11101_staged : normal1_11101 = staged_normal1_11101 := by
  have h : mergeFuel 5000 staged_normal1_111010 staged_normal1_111011 = staged_normal1_11101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_111010_staged normal1_111011_staged).trans h
#print axioms normal1_11101_staged


def staged_normal1_1110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1110_staged : normal1_1110 = staged_normal1_1110 := by
  have h : mergeFuel 5000 staged_normal1_11100 staged_normal1_11101 = staged_normal1_1110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_11100_staged normal1_11101_staged).trans h
#print axioms normal1_1110_staged


def staged_normal1_111100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_111100_staged : normal1_111100 = staged_normal1_111100 := by
  have h : mergeFuel 5000 normal1_1111000 normal1_1111001 = staged_normal1_111100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_1111000) (Eq.refl normal1_1111001)).trans h
#print axioms normal1_111100_staged


def staged_normal1_111101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_111101_staged : normal1_111101 = staged_normal1_111101 := by
  have h : mergeFuel 5000 normal1_1111010 normal1_1111011 = staged_normal1_111101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_1111010) (Eq.refl normal1_1111011)).trans h
#print axioms normal1_111101_staged


def staged_normal1_11110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_11110_staged : normal1_11110 = staged_normal1_11110 := by
  have h : mergeFuel 5000 staged_normal1_111100 staged_normal1_111101 = staged_normal1_11110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_111100_staged normal1_111101_staged).trans h
#print axioms normal1_11110_staged

}
end QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificate
end

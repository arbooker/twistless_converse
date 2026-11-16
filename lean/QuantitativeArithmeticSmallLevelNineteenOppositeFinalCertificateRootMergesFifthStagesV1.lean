module
public import QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateRootMergesFourthStagesV1
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
def staged_normal1_011010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_011010_staged : normal1_011010 = staged_normal1_011010 := by
  have h : mergeFuel 5000 normal1_0110100 normal1_0110101 = staged_normal1_011010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_0110100) (Eq.refl normal1_0110101)).trans h
#print axioms normal1_011010_staged


def staged_normal1_011011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_011011_staged : normal1_011011 = staged_normal1_011011 := by
  have h : mergeFuel 5000 normal1_0110110 normal1_0110111 = staged_normal1_011011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_0110110) (Eq.refl normal1_0110111)).trans h
#print axioms normal1_011011_staged


def staged_normal1_01101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_01101_staged : normal1_01101 = staged_normal1_01101 := by
  have h : mergeFuel 5000 staged_normal1_011010 staged_normal1_011011 = staged_normal1_01101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_011010_staged normal1_011011_staged).trans h
#print axioms normal1_01101_staged


def staged_normal1_0110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_0110_staged : normal1_0110 = staged_normal1_0110 := by
  have h : mergeFuel 5000 staged_normal1_01100 staged_normal1_01101 = staged_normal1_0110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_01100_staged normal1_01101_staged).trans h
#print axioms normal1_0110_staged


def staged_normal1_011100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_011100_staged : normal1_011100 = staged_normal1_011100 := by
  have h : mergeFuel 5000 normal1_0111000 normal1_0111001 = staged_normal1_011100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_0111000) (Eq.refl normal1_0111001)).trans h
#print axioms normal1_011100_staged


def staged_normal1_011101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_011101_staged : normal1_011101 = staged_normal1_011101 := by
  have h : mergeFuel 5000 normal1_0111010 normal1_0111011 = staged_normal1_011101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_0111010) (Eq.refl normal1_0111011)).trans h
#print axioms normal1_011101_staged


def staged_normal1_01110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_01110_staged : normal1_01110 = staged_normal1_01110 := by
  have h : mergeFuel 5000 staged_normal1_011100 staged_normal1_011101 = staged_normal1_01110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_011100_staged normal1_011101_staged).trans h
#print axioms normal1_01110_staged


def staged_normal1_011110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_011110_staged : normal1_011110 = staged_normal1_011110 := by
  have h : mergeFuel 5000 normal1_0111100 normal1_0111101 = staged_normal1_011110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_0111100) (Eq.refl normal1_0111101)).trans h
#print axioms normal1_011110_staged


def staged_normal1_011111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_011111_staged : normal1_011111 = staged_normal1_011111 := by
  have h : mergeFuel 5000 normal1_0111110 normal1_0111111 = staged_normal1_011111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_0111110) (Eq.refl normal1_0111111)).trans h
#print axioms normal1_011111_staged


def staged_normal1_01111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_01111_staged : normal1_01111 = staged_normal1_01111 := by
  have h : mergeFuel 5000 staged_normal1_011110 staged_normal1_011111 = staged_normal1_01111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_011110_staged normal1_011111_staged).trans h
#print axioms normal1_01111_staged


def staged_normal1_0111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_0111_staged : normal1_0111 = staged_normal1_0111 := by
  have h : mergeFuel 5000 staged_normal1_01110 staged_normal1_01111 = staged_normal1_0111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_01110_staged normal1_01111_staged).trans h
#print axioms normal1_0111_staged


def staged_normal1_011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_011_staged : normal1_011 = staged_normal1_011 := by
  have h : mergeFuel 5000 staged_normal1_0110 staged_normal1_0111 = staged_normal1_011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_0110_staged normal1_0111_staged).trans h
#print axioms normal1_011_staged


def staged_normal1_01 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_01_staged : normal1_01 = staged_normal1_01 := by
  have h : mergeFuel 5000 staged_normal1_010 staged_normal1_011 = staged_normal1_01 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_010_staged normal1_011_staged).trans h
#print axioms normal1_01_staged


def staged_normal1_0 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_0_staged : normal1_0 = staged_normal1_0 := by
  have h : mergeFuel 5000 staged_normal1_00 staged_normal1_01 = staged_normal1_0 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_00_staged normal1_01_staged).trans h
#print axioms normal1_0_staged


def staged_normal1_100000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,false,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_100000_staged : normal1_100000 = staged_normal1_100000 := by
  have h : mergeFuel 5000 normal1_1000000 normal1_1000001 = staged_normal1_100000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_1000000) (Eq.refl normal1_1000001)).trans h
#print axioms normal1_100000_staged


def staged_normal1_10000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_10000_staged : normal1_10000 = staged_normal1_10000 := by
  have h : mergeFuel 5000 staged_normal1_100000 normal1_100001 = staged_normal1_10000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_100000_staged (Eq.refl normal1_100001)).trans h
#print axioms normal1_10000_staged


def staged_normal1_10001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_10001_staged : normal1_10001 = staged_normal1_10001 := by
  have h : mergeFuel 5000 normal1_100010 normal1_100011 = staged_normal1_10001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_100010) (Eq.refl normal1_100011)).trans h
#print axioms normal1_10001_staged


def staged_normal1_1000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1000_staged : normal1_1000 = staged_normal1_1000 := by
  have h : mergeFuel 5000 staged_normal1_10000 staged_normal1_10001 = staged_normal1_1000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_10000_staged normal1_10001_staged).trans h
#print axioms normal1_1000_staged


def staged_normal1_10010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_10010_staged : normal1_10010 = staged_normal1_10010 := by
  have h : mergeFuel 5000 normal1_100100 normal1_100101 = staged_normal1_10010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_100100) (Eq.refl normal1_100101)).trans h
#print axioms normal1_10010_staged


def staged_normal1_10011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_10011_staged : normal1_10011 = staged_normal1_10011 := by
  have h : mergeFuel 5000 normal1_100110 normal1_100111 = staged_normal1_10011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_100110) (Eq.refl normal1_100111)).trans h
#print axioms normal1_10011_staged


def staged_normal1_1001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1001_staged : normal1_1001 = staged_normal1_1001 := by
  have h : mergeFuel 5000 staged_normal1_10010 staged_normal1_10011 = staged_normal1_1001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_10010_staged normal1_10011_staged).trans h
#print axioms normal1_1001_staged


def staged_normal1_100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_100_staged : normal1_100 = staged_normal1_100 := by
  have h : mergeFuel 5000 staged_normal1_1000 staged_normal1_1001 = staged_normal1_100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_1000_staged normal1_1001_staged).trans h
#print axioms normal1_100_staged


def staged_normal1_10100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_10100_staged : normal1_10100 = staged_normal1_10100 := by
  have h : mergeFuel 5000 normal1_101000 normal1_101001 = staged_normal1_10100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_101000) (Eq.refl normal1_101001)).trans h
#print axioms normal1_10100_staged


def staged_normal1_10101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_10101_staged : normal1_10101 = staged_normal1_10101 := by
  have h : mergeFuel 5000 normal1_101010 normal1_101011 = staged_normal1_10101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_101010) (Eq.refl normal1_101011)).trans h
#print axioms normal1_10101_staged


def staged_normal1_1010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1010_staged : normal1_1010 = staged_normal1_1010 := by
  have h : mergeFuel 5000 staged_normal1_10100 staged_normal1_10101 = staged_normal1_1010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_10100_staged normal1_10101_staged).trans h
#print axioms normal1_1010_staged


def staged_normal1_10110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_10110_staged : normal1_10110 = staged_normal1_10110 := by
  have h : mergeFuel 5000 normal1_101100 normal1_101101 = staged_normal1_10110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_101100) (Eq.refl normal1_101101)).trans h
#print axioms normal1_10110_staged


def staged_normal1_10111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_10111_staged : normal1_10111 = staged_normal1_10111 := by
  have h : mergeFuel 5000 normal1_101110 normal1_101111 = staged_normal1_10111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_101110) (Eq.refl normal1_101111)).trans h
#print axioms normal1_10111_staged


def staged_normal1_1011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_1011_staged : normal1_1011 = staged_normal1_1011 := by
  have h : mergeFuel 5000 staged_normal1_10110 staged_normal1_10111 = staged_normal1_1011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_10110_staged normal1_10111_staged).trans h
#print axioms normal1_1011_staged


def staged_normal1_101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_101_staged : normal1_101 = staged_normal1_101 := by
  have h : mergeFuel 5000 staged_normal1_1010 staged_normal1_1011 = staged_normal1_101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_1010_staged normal1_1011_staged).trans h
#print axioms normal1_101_staged


def staged_normal1_10 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_10_staged : normal1_10 = staged_normal1_10 := by
  have h : mergeFuel 5000 staged_normal1_100 staged_normal1_101 = staged_normal1_10 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal1_100_staged normal1_101_staged).trans h
#print axioms normal1_10_staged


def staged_normal1_11000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_11000_staged : normal1_11000 = staged_normal1_11000 := by
  have h : mergeFuel 5000 normal1_110000 normal1_110001 = staged_normal1_11000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_110000) (Eq.refl normal1_110001)).trans h
#print axioms normal1_11000_staged


def staged_normal1_11001111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,false,true,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate1)
theorem normal1_11001111_staged : normal1_11001111 = staged_normal1_11001111 := by
  have h : mergeFuel 5000 normal1_110011110 normal1_110011111 = staged_normal1_11001111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal1_110011110) (Eq.refl normal1_110011111)).trans h
#print axioms normal1_11001111_staged

}
end QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificate
end

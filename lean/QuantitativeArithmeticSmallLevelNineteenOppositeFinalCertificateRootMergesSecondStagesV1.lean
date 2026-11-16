module
public import QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateRootMergesFirstStagesV1
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
def staged_normal0_011100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_011100_staged : normal0_011100 = staged_normal0_011100 := by
  have h : mergeFuel 5000 normal0_0111000 normal0_0111001 = staged_normal0_011100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_0111000) (Eq.refl normal0_0111001)).trans h
#print axioms normal0_011100_staged


def staged_normal0_011101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_011101_staged : normal0_011101 = staged_normal0_011101 := by
  have h : mergeFuel 5000 normal0_0111010 normal0_0111011 = staged_normal0_011101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_0111010) (Eq.refl normal0_0111011)).trans h
#print axioms normal0_011101_staged


def staged_normal0_01110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_01110_staged : normal0_01110 = staged_normal0_01110 := by
  have h : mergeFuel 5000 staged_normal0_011100 staged_normal0_011101 = staged_normal0_01110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_011100_staged normal0_011101_staged).trans h
#print axioms normal0_01110_staged


def staged_normal0_011110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_011110_staged : normal0_011110 = staged_normal0_011110 := by
  have h : mergeFuel 5000 normal0_0111100 normal0_0111101 = staged_normal0_011110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_0111100) (Eq.refl normal0_0111101)).trans h
#print axioms normal0_011110_staged


def staged_normal0_011111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_011111_staged : normal0_011111 = staged_normal0_011111 := by
  have h : mergeFuel 5000 normal0_0111110 normal0_0111111 = staged_normal0_011111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_0111110) (Eq.refl normal0_0111111)).trans h
#print axioms normal0_011111_staged


def staged_normal0_01111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_01111_staged : normal0_01111 = staged_normal0_01111 := by
  have h : mergeFuel 5000 staged_normal0_011110 staged_normal0_011111 = staged_normal0_01111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_011110_staged normal0_011111_staged).trans h
#print axioms normal0_01111_staged


def staged_normal0_0111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_0111_staged : normal0_0111 = staged_normal0_0111 := by
  have h : mergeFuel 5000 staged_normal0_01110 staged_normal0_01111 = staged_normal0_0111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_01110_staged normal0_01111_staged).trans h
#print axioms normal0_0111_staged


def staged_normal0_011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_011_staged : normal0_011 = staged_normal0_011 := by
  have h : mergeFuel 5000 staged_normal0_0110 staged_normal0_0111 = staged_normal0_011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_0110_staged normal0_0111_staged).trans h
#print axioms normal0_011_staged


def staged_normal0_01 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_01_staged : normal0_01 = staged_normal0_01 := by
  have h : mergeFuel 5000 staged_normal0_010 staged_normal0_011 = staged_normal0_01 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_010_staged normal0_011_staged).trans h
#print axioms normal0_01_staged


def staged_normal0_0 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_0_staged : normal0_0 = staged_normal0_0 := by
  have h : mergeFuel 5000 staged_normal0_00 staged_normal0_01 = staged_normal0_0 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_00_staged normal0_01_staged).trans h
#print axioms normal0_0_staged


def staged_normal0_100000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,false,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_100000_staged : normal0_100000 = staged_normal0_100000 := by
  have h : mergeFuel 5000 normal0_1000000 normal0_1000001 = staged_normal0_100000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_1000000) (Eq.refl normal0_1000001)).trans h
#print axioms normal0_100000_staged


def staged_normal0_10000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_10000_staged : normal0_10000 = staged_normal0_10000 := by
  have h : mergeFuel 5000 staged_normal0_100000 normal0_100001 = staged_normal0_10000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_100000_staged (Eq.refl normal0_100001)).trans h
#print axioms normal0_10000_staged


def staged_normal0_10001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_10001_staged : normal0_10001 = staged_normal0_10001 := by
  have h : mergeFuel 5000 normal0_100010 normal0_100011 = staged_normal0_10001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_100010) (Eq.refl normal0_100011)).trans h
#print axioms normal0_10001_staged


def staged_normal0_1000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1000_staged : normal0_1000 = staged_normal0_1000 := by
  have h : mergeFuel 5000 staged_normal0_10000 staged_normal0_10001 = staged_normal0_1000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_10000_staged normal0_10001_staged).trans h
#print axioms normal0_1000_staged


def staged_normal0_10010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_10010_staged : normal0_10010 = staged_normal0_10010 := by
  have h : mergeFuel 5000 normal0_100100 normal0_100101 = staged_normal0_10010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_100100) (Eq.refl normal0_100101)).trans h
#print axioms normal0_10010_staged


def staged_normal0_10011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_10011_staged : normal0_10011 = staged_normal0_10011 := by
  have h : mergeFuel 5000 normal0_100110 normal0_100111 = staged_normal0_10011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_100110) (Eq.refl normal0_100111)).trans h
#print axioms normal0_10011_staged


def staged_normal0_1001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1001_staged : normal0_1001 = staged_normal0_1001 := by
  have h : mergeFuel 5000 staged_normal0_10010 staged_normal0_10011 = staged_normal0_1001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_10010_staged normal0_10011_staged).trans h
#print axioms normal0_1001_staged


def staged_normal0_100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_100_staged : normal0_100 = staged_normal0_100 := by
  have h : mergeFuel 5000 staged_normal0_1000 staged_normal0_1001 = staged_normal0_100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_1000_staged normal0_1001_staged).trans h
#print axioms normal0_100_staged


def staged_normal0_10100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_10100_staged : normal0_10100 = staged_normal0_10100 := by
  have h : mergeFuel 5000 normal0_101000 normal0_101001 = staged_normal0_10100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_101000) (Eq.refl normal0_101001)).trans h
#print axioms normal0_10100_staged


def staged_normal0_10101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_10101_staged : normal0_10101 = staged_normal0_10101 := by
  have h : mergeFuel 5000 normal0_101010 normal0_101011 = staged_normal0_10101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_101010) (Eq.refl normal0_101011)).trans h
#print axioms normal0_10101_staged


def staged_normal0_1010 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1010_staged : normal0_1010 = staged_normal0_1010 := by
  have h : mergeFuel 5000 staged_normal0_10100 staged_normal0_10101 = staged_normal0_1010 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_10100_staged normal0_10101_staged).trans h
#print axioms normal0_1010_staged


def staged_normal0_10110 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,true,true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_10110_staged : normal0_10110 = staged_normal0_10110 := by
  have h : mergeFuel 5000 normal0_101100 normal0_101101 = staged_normal0_10110 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_101100) (Eq.refl normal0_101101)).trans h
#print axioms normal0_10110_staged


def staged_normal0_10111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_10111_staged : normal0_10111 = staged_normal0_10111 := by
  have h : mergeFuel 5000 normal0_101110 normal0_101111 = staged_normal0_10111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_101110) (Eq.refl normal0_101111)).trans h
#print axioms normal0_10111_staged


def staged_normal0_1011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1011_staged : normal0_1011 = staged_normal0_1011 := by
  have h : mergeFuel 5000 staged_normal0_10110 staged_normal0_10111 = staged_normal0_1011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_10110_staged normal0_10111_staged).trans h
#print axioms normal0_1011_staged


def staged_normal0_101 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_101_staged : normal0_101 = staged_normal0_101 := by
  have h : mergeFuel 5000 staged_normal0_1010 staged_normal0_1011 = staged_normal0_101 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_1010_staged normal0_1011_staged).trans h
#print axioms normal0_101_staged


def staged_normal0_10 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_10_staged : normal0_10 = staged_normal0_10 := by
  have h : mergeFuel 5000 staged_normal0_100 staged_normal0_101 = staged_normal0_10 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_100_staged normal0_101_staged).trans h
#print axioms normal0_10_staged


def staged_normal0_11000 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_11000_staged : normal0_11000 = staged_normal0_11000 := by
  have h : mergeFuel 5000 normal0_110000 normal0_110001 = staged_normal0_11000 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_110000) (Eq.refl normal0_110001)).trans h
#print axioms normal0_11000_staged


def staged_normal0_11001111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,false,true,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_11001111_staged : normal0_11001111 = staged_normal0_11001111 := by
  have h : mergeFuel 5000 normal0_110011110 normal0_110011111 = staged_normal0_11001111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_110011110) (Eq.refl normal0_110011111)).trans h
#print axioms normal0_11001111_staged


def staged_normal0_1100111 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,false,true,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1100111_staged : normal0_1100111 = staged_normal0_1100111 := by
  have h : mergeFuel 5000 normal0_11001110 staged_normal0_11001111 = staged_normal0_1100111 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_11001110) normal0_11001111_staged).trans h
#print axioms normal0_1100111_staged


def staged_normal0_110011 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,false,true,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_110011_staged : normal0_110011 = staged_normal0_110011 := by
  have h : mergeFuel 5000 normal0_1100110 staged_normal0_1100111 = staged_normal0_110011 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_1100110) normal0_1100111_staged).trans h
#print axioms normal0_110011_staged


def staged_normal0_11001 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,false,true] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_11001_staged : normal0_11001 = staged_normal0_11001 := by
  have h : mergeFuel 5000 normal0_110010 staged_normal0_110011 = staged_normal0_11001 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) (Eq.refl normal0_110010) normal0_110011_staged).trans h
#print axioms normal0_11001_staged


def staged_normal0_1100 : Poly := eval% computeCombine QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.inputs
  (descend [true,true,false,false] QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificateCompute.certificate0)
theorem normal0_1100_staged : normal0_1100 = staged_normal0_1100 := by
  have h : mergeFuel 5000 staged_normal0_11000 staged_normal0_11001 = staged_normal0_1100 := by decide +kernel
  exact (congrArg₂ (mergeFuel 5000) normal0_11000_staged normal0_11001_staged).trans h
#print axioms normal0_1100_staged

}
end QuantitativeArithmeticSmallLevelNineteenOppositeFinalCertificate
end

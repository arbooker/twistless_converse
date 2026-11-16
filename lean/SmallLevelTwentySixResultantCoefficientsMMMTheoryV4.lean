module
public meta import QuantitativeArithmeticSparseCertificateComputeV5
public meta import SmallLevelCertificateBatchCommandV1
public meta import SmallLevelSparsePolynomialLiteralV1

public import QuantitativeArithmeticSparsePolynomialCertificateTheoryV4
public import SmallLevelPolynomialCoefficientAssemblyV1
public import SmallLevelSparseCoefficientAssemblyV1
public import SmallLevelSparseCoefficientPartitionV1
public import SmallLevelTwentySixResultantPolynomialDataV1
public import SmallLevelTwentySixWeightAbelMMMDataV1
public meta import QuantitativeArithmeticCompactCommandsV1

public import SmallLevelTwentySixResultantCoefficientsMMMCertificateDataV1
public import SmallLevelTwentySixResultantCoefficientsMMMSlicesV1
public import SmallLevelTwentySixResultantCoefficientsMMMRowZeroV1
public import SmallLevelTwentySixResultantCoefficientsMMMRowOneV1
public import SmallLevelTwentySixResultantCoefficientsMMMRowTwoV1
set_option Elab.async false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false


certificate_batch {
/-! ## SmallLevelTwentySixResultantCoefficientsMMMRowIndexXIndexBridgeSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

namespace SmallLevelTwentySixResultantCoefficientsMMM
open Complex Polynomial SmallLevelPolynomialCoefficientAssembly
open scoped Classical
theorem row0_coefficient00 (y z w : ℂ) : (rowPoly0 y z w).coeff 0=(dPoly0 y z w).coeff 0 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x00 y z w


theorem row0_coefficient01 (y z w : ℂ) : (rowPoly0 y z w).coeff 1=(dPoly0 y z w).coeff 1 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x01 y z w


theorem row0_coefficient02 (y z w : ℂ) : (rowPoly0 y z w).coeff 2=(dPoly0 y z w).coeff 2 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x02 y z w


theorem row0_coefficient03 (y z w : ℂ) : (rowPoly0 y z w).coeff 3=(dPoly0 y z w).coeff 3 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x03 y z w


theorem row0_coefficient04 (y z w : ℂ) : (rowPoly0 y z w).coeff 4=(dPoly0 y z w).coeff 4 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x04 y z w


theorem row0_coefficient05 (y z w : ℂ) : (rowPoly0 y z w).coeff 5=(dPoly0 y z w).coeff 5 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x05 y z w


theorem row0_coefficient06 (y z w : ℂ) : (rowPoly0 y z w).coeff 6=(dPoly0 y z w).coeff 6 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x06 y z w


theorem row0_coefficient07 (y z w : ℂ) : (rowPoly0 y z w).coeff 7=(dPoly0 y z w).coeff 7 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x07 y z w


theorem row0_coefficient08 (y z w : ℂ) : (rowPoly0 y z w).coeff 8=(dPoly0 y z w).coeff 8 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x08 y z w


theorem row0_coefficient09 (y z w : ℂ) : (rowPoly0 y z w).coeff 9=(dPoly0 y z w).coeff 9 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x09 y z w


theorem row0_coefficient10 (y z w : ℂ) : (rowPoly0 y z w).coeff 10=(dPoly0 y z w).coeff 10 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x10 y z w


theorem row0_coefficient11 (y z w : ℂ) : (rowPoly0 y z w).coeff 11=(dPoly0 y z w).coeff 11 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x11 y z w


theorem row0_coefficient12 (y z w : ℂ) : (rowPoly0 y z w).coeff 12=(dPoly0 y z w).coeff 12 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x12 y z w


theorem row0_coefficient13 (y z w : ℂ) : (rowPoly0 y z w).coeff 13=(dPoly0 y z w).coeff 13 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x13 y z w


theorem row0_coefficient14 (y z w : ℂ) : (rowPoly0 y z w).coeff 14=(dPoly0 y z w).coeff 14 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x14 y z w


theorem row0_coefficient15 (y z w : ℂ) : (rowPoly0 y z w).coeff 15=(dPoly0 y z w).coeff 15 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x15 y z w


theorem row0_coefficient16 (y z w : ℂ) : (rowPoly0 y z w).coeff 16=(dPoly0 y z w).coeff 16 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x16 y z w


theorem row0_coefficient17 (y z w : ℂ) : (rowPoly0 y z w).coeff 17=(dPoly0 y z w).coeff 17 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x17 y z w


theorem row0_coefficient18 (y z w : ℂ) : (rowPoly0 y z w).coeff 18=(dPoly0 y z w).coeff 18 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x18 y z w


theorem row0_coefficient19 (y z w : ℂ) : (rowPoly0 y z w).coeff 19=(dPoly0 y z w).coeff 19 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x19 y z w


theorem row0_coefficient20 (y z w : ℂ) : (rowPoly0 y z w).coeff 20=(dPoly0 y z w).coeff 20 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x20 y z w


theorem row0_coefficient21 (y z w : ℂ) : (rowPoly0 y z w).coeff 21=(dPoly0 y z w).coeff 21 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x21 y z w


theorem row0_coefficient22 (y z w : ℂ) : (rowPoly0 y z w).coeff 22=(dPoly0 y z w).coeff 22 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x22 y z w


theorem row0_coefficient23 (y z w : ℂ) : (rowPoly0 y z w).coeff 23=(dPoly0 y z w).coeff 23 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x23 y z w


theorem row0_coefficient24 (y z w : ℂ) : (rowPoly0 y z w).coeff 24=(dPoly0 y z w).coeff 24 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x24 y z w


theorem row0_coefficient25 (y z w : ℂ) : (rowPoly0 y z w).coeff 25=(dPoly0 y z w).coeff 25 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x25 y z w


theorem row0_coefficient26 (y z w : ℂ) : (rowPoly0 y z w).coeff 26=(dPoly0 y z w).coeff 26 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x26 y z w


theorem row0_coefficient27 (y z w : ℂ) : (rowPoly0 y z w).coeff 27=(dPoly0 y z w).coeff 27 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x27 y z w


theorem row0_coefficient28 (y z w : ℂ) : (rowPoly0 y z w).coeff 28=(dPoly0 y z w).coeff 28 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x28 y z w


theorem row0_coefficient29 (y z w : ℂ) : (rowPoly0 y z w).coeff 29=(dPoly0 y z w).coeff 29 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x29 y z w


theorem row0_coefficient30 (y z w : ℂ) : (rowPoly0 y z w).coeff 30=(dPoly0 y z w).coeff 30 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x30 y z w


theorem row0_coefficient31 (y z w : ℂ) : (rowPoly0 y z w).coeff 31=(dPoly0 y z w).coeff 31 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x31 y z w


theorem row0_coefficient32 (y z w : ℂ) : (rowPoly0 y z w).coeff 32=(dPoly0 y z w).coeff 32 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x32 y z w


theorem row0_coefficient33 (y z w : ℂ) : (rowPoly0 y z w).coeff 33=(dPoly0 y z w).coeff 33 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x33 y z w


theorem row0_coefficient34 (y z w : ℂ) : (rowPoly0 y z w).coeff 34=(dPoly0 y z w).coeff 34 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x34 y z w


theorem row0_coefficient35 (y z w : ℂ) : (rowPoly0 y z w).coeff 35=(dPoly0 y z w).coeff 35 := by
  simpa [rowPoly0,qPoly0,rPoly0,qPoly4,vPoly0,dPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row0_x35 y z w


theorem row1_coefficient00 (y z w : ℂ) : (rowPoly1 y z w).coeff 0=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x00 y z w


theorem row1_coefficient01 (y z w : ℂ) : (rowPoly1 y z w).coeff 1=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x01 y z w


theorem row1_coefficient02 (y z w : ℂ) : (rowPoly1 y z w).coeff 2=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x02 y z w


theorem row1_coefficient03 (y z w : ℂ) : (rowPoly1 y z w).coeff 3=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x03 y z w


theorem row1_coefficient04 (y z w : ℂ) : (rowPoly1 y z w).coeff 4=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x04 y z w


theorem row1_coefficient05 (y z w : ℂ) : (rowPoly1 y z w).coeff 5=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x05 y z w


theorem row1_coefficient06 (y z w : ℂ) : (rowPoly1 y z w).coeff 6=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x06 y z w


theorem row1_coefficient07 (y z w : ℂ) : (rowPoly1 y z w).coeff 7=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x07 y z w


theorem row1_coefficient08 (y z w : ℂ) : (rowPoly1 y z w).coeff 8=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x08 y z w


theorem row1_coefficient09 (y z w : ℂ) : (rowPoly1 y z w).coeff 9=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x09 y z w


theorem row1_coefficient10 (y z w : ℂ) : (rowPoly1 y z w).coeff 10=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x10 y z w


theorem row1_coefficient11 (y z w : ℂ) : (rowPoly1 y z w).coeff 11=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x11 y z w


theorem row1_coefficient12 (y z w : ℂ) : (rowPoly1 y z w).coeff 12=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x12 y z w


theorem row1_coefficient13 (y z w : ℂ) : (rowPoly1 y z w).coeff 13=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x13 y z w


theorem row1_coefficient14 (y z w : ℂ) : (rowPoly1 y z w).coeff 14=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x14 y z w


theorem row1_coefficient15 (y z w : ℂ) : (rowPoly1 y z w).coeff 15=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x15 y z w


theorem row1_coefficient16 (y z w : ℂ) : (rowPoly1 y z w).coeff 16=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x16 y z w



theorem row2_coefficient10 (y z w : ℂ) : (rowPoly2 y z w).coeff 10=0 := by
  simpa [rowPoly2,qPoly0,qPoly1,qPoly2,qPoly4,qPoly5,qPoly6,
    rPoly0,rPoly1,rPoly2,vPoly0,vPoly1,vPoly2,coeff_add,coeff_mul_range,
    Finset.sum_range_succ,add_assoc] using row2_x10 y z w

end SmallLevelTwentySixResultantCoefficientsMMM
end
end
end

/-! ## SmallLevelTwentySixResultantCoefficientsMMMTheoryV4 -/
section
/-! Consolidated chapter: SmallLevelTwentySixResultantCoefficientsMMM. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixResultantCoefficientsMMMAbelBridgeV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option maxHeartbeats 5000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixResultantCoefficientsMMM
open Complex QuantitativeArithmeticSparsePolynomialCertificate
open SmallLevelSparseCoefficientPartition SmallLevelSparsePolynomialNormalize
theorem abel_bounded : bounded 36 SmallLevelTwentySixWeightAbelMMM.terms=true := by bounded_sparse_data

theorem coefficient_slice_eval (y z w : ℂ) (i : Fin 36) :
    eval y z w 1 1 (slice i SmallLevelTwentySixWeightAbelMMM.terms)=eval y z w 1 1 (coefficientData i) := by
  fin_cases i
  · exact slice00_eval y z w
  · exact slice01_eval y z w
  · exact slice02_eval y z w
  · exact slice03_eval y z w
  · exact slice04_eval y z w
  · exact slice05_eval y z w
  · exact slice06_eval y z w
  · exact slice07_eval y z w
  · exact slice08_eval y z w
  · exact slice09_eval y z w
  · exact slice10_eval y z w
  · exact slice11_eval y z w
  · exact slice12_eval y z w
  · exact slice13_eval y z w
  · exact slice14_eval y z w
  · exact slice15_eval y z w
  · exact slice16_eval y z w
  · exact slice17_eval y z w
  · exact slice18_eval y z w
  · exact slice19_eval y z w
  · exact slice20_eval y z w
  · exact slice21_eval y z w
  · exact slice22_eval y z w
  · exact slice23_eval y z w
  · exact slice24_eval y z w
  · exact slice25_eval y z w
  · exact slice26_eval y z w
  · exact slice27_eval y z w
  · exact slice28_eval y z w
  · exact slice29_eval y z w
  · exact slice30_eval y z w
  · exact slice31_eval y z w
  · exact slice32_eval y z w
  · exact slice33_eval y z w
  · exact slice34_eval y z w
  · exact slice35_eval y z w

theorem d_eval_eq_abel (x y z w : ℂ) :
    (dPoly0 y z w).eval x=eval x y z w 1 SmallLevelTwentySixWeightAbelMMM.terms := by
  have hp := eval_partition 36 SmallLevelTwentySixWeightAbelMMM.terms abel_bounded x y z w
  have hd := SmallLevelSparseCoefficientAssembly.assemble_eval_polynomial coefficientData x y z w 1
  rw [coefficient_polynomial] at hd
  calc
    (dPoly0 y z w).eval x=eval x y z w 1 (SmallLevelSparseCoefficientAssembly.assemble coefficientData) := hd.symm
    _=∑ i : Fin 36,x^(i:ℕ)*eval y z w 1 1 (coefficientData i) :=
      SmallLevelSparseCoefficientAssembly.eval_assemble coefficientData x y z w 1
    _=∑ i : Fin 36,x^(i:ℕ)*eval y z w 1 1 (slice i SmallLevelTwentySixWeightAbelMMM.terms) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [coefficient_slice_eval]
    _=eval x y z w 1 SmallLevelTwentySixWeightAbelMMM.terms := hp.symm

end SmallLevelTwentySixResultantCoefficientsMMM
end
end

/-! ## SmallLevelTwentySixResultantCoefficientsMMMBoundsV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelTwentySixResultantCoefficientsMMM
open Complex Polynomial
open scoped Classical

theorem qPoly0_bound (y z w : ℂ) : (qPoly0 y z w).natDegree≤30 :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide : 1≤31) _)

theorem qPoly1_bound (y z w : ℂ) : (qPoly1 y z w).natDegree≤29 :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide : 1≤30) _)

theorem qPoly2_bound (y z w : ℂ) : (qPoly2 y z w).natDegree≤28 :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide : 1≤29) _)

theorem qPoly3_bound (y z w : ℂ) : (qPoly3 y z w).natDegree≤27 :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide : 1≤28) _)

theorem qPoly4_bound (y z w : ℂ) : (qPoly4 y z w).natDegree≤24 :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide : 1≤25) _)

theorem qPoly5_bound (y z w : ℂ) : (qPoly5 y z w).natDegree≤23 :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide : 1≤24) _)

theorem qPoly6_bound (y z w : ℂ) : (qPoly6 y z w).natDegree≤22 :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide : 1≤23) _)

theorem rPoly0_bound (y z w : ℂ) : (rPoly0 y z w).natDegree≤5 :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide : 1≤6) _)

theorem rPoly1_bound (y z w : ℂ) : (rPoly1 y z w).natDegree≤3 :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide : 1≤4) _)

theorem rPoly2_bound (y z w : ℂ) : (rPoly2 y z w).natDegree≤2 :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide : 1≤3) _)

theorem rPoly3_bound (y z w : ℂ) : (rPoly3 y z w).natDegree≤1 :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide : 1≤2) _)

theorem vPoly0_bound (y z w : ℂ) : (vPoly0 y z w).natDegree≤11 :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide : 1≤12) _)

theorem vPoly1_bound (y z w : ℂ) : (vPoly1 y z w).natDegree≤10 :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide : 1≤11) _)

theorem vPoly2_bound (y z w : ℂ) : (vPoly2 y z w).natDegree≤8 :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide : 1≤9) _)

theorem vPoly3_bound (y z w : ℂ) : (vPoly3 y z w).natDegree≤7 :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide : 1≤8) _)

theorem vPoly4_bound (y z w : ℂ) : (vPoly4 y z w).natDegree≤6 :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide : 1≤7) _)

theorem dPoly0_bound (y z w : ℂ) : (dPoly0 y z w).natDegree≤35 :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide : 1≤36) _)

theorem rowPoly0_bound (y z w : ℂ) : (rowPoly0 y z w).natDegree<36 := by
  have h0 : (qPoly0 y z w*rPoly0 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly0 y z w) (q := rPoly0 y z w)
    have hq := qPoly0_bound y z w
    have hr := rPoly0_bound y z w
    omega
  have h1 : (qPoly4 y z w*vPoly0 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly4 y z w) (q := vPoly0 y z w)
    have hq := qPoly4_bound y z w
    have hr := vPoly0_bound y z w
    omega
  exact Nat.lt_succ_of_le (Polynomial.natDegree_add_le_of_degree_le h0 h1)

theorem rowPoly1_bound (y z w : ℂ) : (rowPoly1 y z w).natDegree<36 := by
  have h0 : (qPoly0 y z w*rPoly1 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly0 y z w) (q := rPoly1 y z w)
    have hq := qPoly0_bound y z w
    have hr := rPoly1_bound y z w
    omega
  have h1 : (qPoly1 y z w*rPoly0 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly1 y z w) (q := rPoly0 y z w)
    have hq := qPoly1_bound y z w
    have hr := rPoly0_bound y z w
    omega
  have h2 : (qPoly4 y z w*vPoly1 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly4 y z w) (q := vPoly1 y z w)
    have hq := qPoly4_bound y z w
    have hr := vPoly1_bound y z w
    omega
  have h3 : (qPoly5 y z w*vPoly0 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly5 y z w) (q := vPoly0 y z w)
    have hq := qPoly5_bound y z w
    have hr := vPoly0_bound y z w
    omega
  exact Nat.lt_succ_of_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le h0 h1) h2) h3)

theorem rowPoly2_bound (y z w : ℂ) : (rowPoly2 y z w).natDegree<36 := by
  have h0 : (qPoly0 y z w*rPoly2 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly0 y z w) (q := rPoly2 y z w)
    have hq := qPoly0_bound y z w
    have hr := rPoly2_bound y z w
    omega
  have h1 : (qPoly1 y z w*rPoly1 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly1 y z w) (q := rPoly1 y z w)
    have hq := qPoly1_bound y z w
    have hr := rPoly1_bound y z w
    omega
  have h2 : (qPoly2 y z w*rPoly0 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly2 y z w) (q := rPoly0 y z w)
    have hq := qPoly2_bound y z w
    have hr := rPoly0_bound y z w
    omega
  have h3 : (qPoly4 y z w*vPoly2 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly4 y z w) (q := vPoly2 y z w)
    have hq := qPoly4_bound y z w
    have hr := vPoly2_bound y z w
    omega
  have h4 : (qPoly5 y z w*vPoly1 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly5 y z w) (q := vPoly1 y z w)
    have hq := qPoly5_bound y z w
    have hr := vPoly1_bound y z w
    omega
  have h5 : (qPoly6 y z w*vPoly0 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly6 y z w) (q := vPoly0 y z w)
    have hq := qPoly6_bound y z w
    have hr := vPoly0_bound y z w
    omega
  exact Nat.lt_succ_of_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le h0 h1) h2) h3) h4) h5)

theorem rowPoly3_bound (y z w : ℂ) : (rowPoly3 y z w).natDegree<36 := by
  have h0 : (qPoly0 y z w*rPoly3 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly0 y z w) (q := rPoly3 y z w)
    have hq := qPoly0_bound y z w
    have hr := rPoly3_bound y z w
    omega
  have h1 : (qPoly1 y z w*rPoly2 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly1 y z w) (q := rPoly2 y z w)
    have hq := qPoly1_bound y z w
    have hr := rPoly2_bound y z w
    omega
  have h2 : (qPoly2 y z w*rPoly1 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly2 y z w) (q := rPoly1 y z w)
    have hq := qPoly2_bound y z w
    have hr := rPoly1_bound y z w
    omega
  have h3 : (qPoly3 y z w*rPoly0 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly3 y z w) (q := rPoly0 y z w)
    have hq := qPoly3_bound y z w
    have hr := rPoly0_bound y z w
    omega
  have h4 : (qPoly4 y z w*vPoly3 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly4 y z w) (q := vPoly3 y z w)
    have hq := qPoly4_bound y z w
    have hr := vPoly3_bound y z w
    omega
  have h5 : (qPoly5 y z w*vPoly2 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly5 y z w) (q := vPoly2 y z w)
    have hq := qPoly5_bound y z w
    have hr := vPoly2_bound y z w
    omega
  have h6 : (qPoly6 y z w*vPoly1 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly6 y z w) (q := vPoly1 y z w)
    have hq := qPoly6_bound y z w
    have hr := vPoly1_bound y z w
    omega
  exact Nat.lt_succ_of_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le h0 h1) h2) h3) h4) h5) h6)

theorem rowPoly4_bound (y z w : ℂ) : (rowPoly4 y z w).natDegree<36 := by
  have h0 : (qPoly1 y z w*rPoly3 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly1 y z w) (q := rPoly3 y z w)
    have hq := qPoly1_bound y z w
    have hr := rPoly3_bound y z w
    omega
  have h1 : (qPoly2 y z w*rPoly2 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly2 y z w) (q := rPoly2 y z w)
    have hq := qPoly2_bound y z w
    have hr := rPoly2_bound y z w
    omega
  have h2 : (qPoly3 y z w*rPoly1 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly3 y z w) (q := rPoly1 y z w)
    have hq := qPoly3_bound y z w
    have hr := rPoly1_bound y z w
    omega
  have h3 : (qPoly4 y z w*vPoly4 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly4 y z w) (q := vPoly4 y z w)
    have hq := qPoly4_bound y z w
    have hr := vPoly4_bound y z w
    omega
  have h4 : (qPoly5 y z w*vPoly3 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly5 y z w) (q := vPoly3 y z w)
    have hq := qPoly5_bound y z w
    have hr := vPoly3_bound y z w
    omega
  have h5 : (qPoly6 y z w*vPoly2 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly6 y z w) (q := vPoly2 y z w)
    have hq := qPoly6_bound y z w
    have hr := vPoly2_bound y z w
    omega
  exact Nat.lt_succ_of_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le h0 h1) h2) h3) h4) h5)

theorem rowPoly5_bound (y z w : ℂ) : (rowPoly5 y z w).natDegree<36 := by
  have h0 : (qPoly2 y z w*rPoly3 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly2 y z w) (q := rPoly3 y z w)
    have hq := qPoly2_bound y z w
    have hr := rPoly3_bound y z w
    omega
  have h1 : (qPoly3 y z w*rPoly2 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly3 y z w) (q := rPoly2 y z w)
    have hq := qPoly3_bound y z w
    have hr := rPoly2_bound y z w
    omega
  have h2 : (qPoly5 y z w*vPoly4 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly5 y z w) (q := vPoly4 y z w)
    have hq := qPoly5_bound y z w
    have hr := vPoly4_bound y z w
    omega
  have h3 : (qPoly6 y z w*vPoly3 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly6 y z w) (q := vPoly3 y z w)
    have hq := qPoly6_bound y z w
    have hr := vPoly3_bound y z w
    omega
  exact Nat.lt_succ_of_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le h0 h1) h2) h3)

theorem rowPoly6_bound (y z w : ℂ) : (rowPoly6 y z w).natDegree<36 := by
  have h0 : (qPoly3 y z w*rPoly3 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly3 y z w) (q := rPoly3 y z w)
    have hq := qPoly3_bound y z w
    have hr := rPoly3_bound y z w
    omega
  have h1 : (qPoly6 y z w*vPoly4 y z w).natDegree≤35 := by
    have h := Polynomial.natDegree_mul_le (p := qPoly6 y z w) (q := vPoly4 y z w)
    have hq := qPoly6_bound y z w
    have hr := vPoly4_bound y z w
    omega
  exact Nat.lt_succ_of_le (Polynomial.natDegree_add_le_of_degree_le h0 h1)

end SmallLevelTwentySixResultantCoefficientsMMM
end
end

/-! ## SmallLevelTwentySixResultantCoefficientsMMMOriginalBridgeV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentySixResultantCoefficientsMMM
open Complex
open scoped Classical

theorem r_evaluation (x y z w a : ℂ) :
    (rPoly0 y z w).eval x + (rPoly1 y z w).eval x*a + (rPoly2 y z w).eval x*a^2 + (rPoly3 y z w).eval x*a^3=SmallLevelTwentySixUnitMMM.WeightResultants.r x y z w a 0 0 := by
  norm_num [rPoly0,rPoly1,rPoly2,rPoly3,r0000Block00,r0000Data,r0000,r0001Block00,r0001Data,r0001,r0002Block00,r0002Data,r0002,r0003Block00,r0003Data,r0003,r0005Block00,r0005Data,r0005,r0100Block00,r0100Data,r0100,r0101Block00,r0101Data,r0101,r0102Block00,r0102Data,r0102,r0103Block00,r0103Data,r0103,r0200Block00,r0200Data,r0200,r0201Block00,r0201Data,r0201,r0202Block00,r0202Data,r0202,r0300Block00,r0300Data,r0300,r0301Block00,r0301Data,r0301,Polynomial.ofFn_eq_sum_monomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial,Fin.sum_univ_succ,QuantitativeArithmeticSparsePolynomialCertificate.eval,QuantitativeArithmeticSparsePolynomialCertificate.monomial,SmallLevelTwentySixUnitMMM.WeightResultants.r] <;> ring



theorem v_evaluation (x y z w a : ℂ) :
    (vPoly0 y z w).eval x + (vPoly1 y z w).eval x*a + (vPoly2 y z w).eval x*a^2 + (vPoly3 y z w).eval x*a^3 + (vPoly4 y z w).eval x*a^4=SmallLevelTwentySixUnitMMM.WeightResultants.v x y z w a 0 0 := by
  norm_num [vPoly0,vPoly1,vPoly2,vPoly3,vPoly4,v0000Block00,v0000Data,v0000,v0001Block00,v0001Data,v0001,v0002Block00,v0002Data,v0002,v0003Block00,v0003Data,v0003,v0004Block00,v0004Data,v0004,v0005Block00,v0005Data,v0005,v0006Block00,v0006Data,v0006,v0007Block00,v0007Data,v0007,v0008Block00,v0008Data,v0008,v0009Block00,v0009Data,v0009,v0010Block00,v0010Data,v0010,v0011Block00,v0011Data,v0011,v0100Block00,v0100Data,v0100,v0101Block00,v0101Data,v0101,v0102Block00,v0102Data,v0102,v0103Block00,v0103Data,v0103,v0104Block00,v0104Data,v0104,v0105Block00,v0105Data,v0105,v0106Block00,v0106Data,v0106,v0107Block00,v0107Data,v0107,v0108Block00,v0108Data,v0108,v0109Block00,v0109Data,v0109,v0110Block00,v0110Data,v0110,v0200Block00,v0200Data,v0200,v0201Block00,v0201Data,v0201,v0202Block00,v0202Data,v0202,v0203Block00,v0203Data,v0203,v0204Block00,v0204Data,v0204,v0205Block00,v0205Data,v0205,v0206Block00,v0206Data,v0206,v0207Block00,v0207Data,v0207,v0208Block00,v0208Data,v0208,v0301Block00,v0301Data,v0301,v0302Block00,v0302Data,v0302,v0303Block00,v0303Data,v0303,v0304Block00,v0304Data,v0304,v0305Block00,v0305Data,v0305,v0306Block00,v0306Data,v0306,v0307Block00,v0307Data,v0307,v0401Block00,v0401Data,v0401,v0402Block00,v0402Data,v0402,v0403Block00,v0403Data,v0403,v0404Block00,v0404Data,v0404,v0405Block00,v0405Data,v0405,v0406Block00,v0406Data,v0406,Polynomial.ofFn_eq_sum_monomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial,Fin.sum_univ_succ,QuantitativeArithmeticSparsePolynomialCertificate.eval,QuantitativeArithmeticSparsePolynomialCertificate.monomial,SmallLevelTwentySixUnitMMM.WeightResultants.v] <;> ring


end SmallLevelTwentySixResultantCoefficientsMMM
end
end

/-! ## SmallLevelTwentySixResultantCoefficientsMMMRow0IdentityV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixResultantCoefficientsMMM
open Complex Polynomial SmallLevelPolynomialCoefficientAssembly
open scoped Classical
theorem row0_identity (y z w : ℂ) : rowPoly0 y z w=dPoly0 y z w := by
  apply eq_of_bounded_coefficients _ _ 36
    (rowPoly0_bound y z w) (Nat.lt_succ_of_le (dPoly0_bound y z w))
  intro i
  fin_cases i
  · exact row0_coefficient00 y z w
  · exact row0_coefficient01 y z w
  · exact row0_coefficient02 y z w
  · exact row0_coefficient03 y z w
  · exact row0_coefficient04 y z w
  · exact row0_coefficient05 y z w
  · exact row0_coefficient06 y z w
  · exact row0_coefficient07 y z w
  · exact row0_coefficient08 y z w
  · exact row0_coefficient09 y z w
  · exact row0_coefficient10 y z w
  · exact row0_coefficient11 y z w
  · exact row0_coefficient12 y z w
  · exact row0_coefficient13 y z w
  · exact row0_coefficient14 y z w
  · exact row0_coefficient15 y z w
  · exact row0_coefficient16 y z w
  · exact row0_coefficient17 y z w
  · exact row0_coefficient18 y z w
  · exact row0_coefficient19 y z w
  · exact row0_coefficient20 y z w
  · exact row0_coefficient21 y z w
  · exact row0_coefficient22 y z w
  · exact row0_coefficient23 y z w
  · exact row0_coefficient24 y z w
  · exact row0_coefficient25 y z w
  · exact row0_coefficient26 y z w
  · exact row0_coefficient27 y z w
  · exact row0_coefficient28 y z w
  · exact row0_coefficient29 y z w
  · exact row0_coefficient30 y z w
  · exact row0_coefficient31 y z w
  · exact row0_coefficient32 y z w
  · exact row0_coefficient33 y z w
  · exact row0_coefficient34 y z w
  · exact row0_coefficient35 y z w

end SmallLevelTwentySixResultantCoefficientsMMM
end
end
end

}
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice00_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice01_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice02_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice03_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice04_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice05_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice06_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice07_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice08_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice09_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice10_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice11_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice12_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice13_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice14_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice15_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice16_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice17_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice18_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice19_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice20_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice21_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice22_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice23_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice24_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice25_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice26_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice27_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice28_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice29_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice30_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice31_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice32_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice33_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice34_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.slice35_eval
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x00
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x01
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x02
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x03
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x04
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x05
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x06
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x07
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x08
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x09
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x10
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x11
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x12
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x13
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x14
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x15
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x16
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x17
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x18
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x19
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x20
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x21
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x22
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x23
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x24
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x25
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x26
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x27
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x28
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x29
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x30
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x31
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x32
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x33
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x34
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_x35
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_x00
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_x01
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_x02
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_x03
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_x04
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_x05
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_x06
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_x07
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_x08
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_x09
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_x10
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_x11
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_x12
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_x13
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_x14
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_x15
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_x16
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row2_x10
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient00
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient01
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient02
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient03
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient04
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient05
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient06
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient07
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient08
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient09
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient10
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient11
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient12
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient13
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient14
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient15
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient16
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient17
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient18
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient19
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient20
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient21
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient22
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient23
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient24
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient25
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient26
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient27
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient28
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient29
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient30
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient31
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient32
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient33
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient34
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_coefficient35
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_coefficient00
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_coefficient01
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_coefficient02
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_coefficient03
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_coefficient04
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_coefficient05
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_coefficient06
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_coefficient07
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_coefficient08
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_coefficient09
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_coefficient10
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_coefficient11
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_coefficient12
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_coefficient13
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_coefficient14
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_coefficient15
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row1_coefficient16
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row2_coefficient10
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.d_eval_eq_abel
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.rowPoly0_bound
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.rowPoly6_bound
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.r_evaluation
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.v_evaluation
#print axioms SmallLevelTwentySixResultantCoefficientsMMM.row0_identity

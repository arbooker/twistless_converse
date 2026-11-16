module

public import QuantitativeArithmeticSparsePolynomialCertificateTheoryV4
public import SmallLevelCubicQuarticSylvesterV1
public import SmallLevelTwentySixResultantBatchedMMMZeroGroupedTheoryV4
public import SmallLevelTwentySixResultantCoefficientsMMMTheoryV4
public meta import QuantitativeArithmeticCompactCommandsV1

public import SmallLevelTwentySixResultantMMMRow1StagesV6
public import SmallLevelTwentySixResultantMMMRow2StagesV6
public import SmallLevelTwentySixResultantMMMRow3StagesV6
public import SmallLevelTwentySixResultantMMMRow4StagesV6
public import SmallLevelTwentySixResultantMMMRow5StagesV6
public import SmallLevelTwentySixResultantMMMRow6StagesV6

/-! ## SmallLevelTwentySixResultantBatchedMMMRowIndexIdentitySeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

namespace SmallLevelTwentySixResultantBatchedMMM
open Complex Polynomial SmallLevelPolynomialCoefficientAssembly
open SmallLevelTwentySixResultantCoefficientsMMM
open scoped Classical
theorem row1_identity (y z w : ℂ) : rowPoly1 y z w=0 := by
  apply eq_of_bounded_coefficients _ _ 36
    (rowPoly1_bound y z w) (by norm_num)
  intro i
  fin_cases i
  · simpa only [Polynomial.coeff_zero] using row1_coefficient00 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient01 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient02 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient03 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient04 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient05 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient06 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient07 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient08 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient09 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient10 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient11 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient12 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient13 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient14 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient15 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient16 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient17 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient18 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient19 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient20 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient21 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient22 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient23 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient24 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient25 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient26 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient27 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient28 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient29 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient30 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient31 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient32 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient33 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient34 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient35 y z w

#print axioms row1_identity
end SmallLevelTwentySixResultantBatchedMMM
end

section
set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

namespace SmallLevelTwentySixResultantBatchedMMM
open Complex Polynomial SmallLevelPolynomialCoefficientAssembly
open SmallLevelTwentySixResultantCoefficientsMMM
open scoped Classical
theorem row2_identity (y z w : ℂ) : rowPoly2 y z w=0 := by
  apply eq_of_bounded_coefficients _ _ 36
    (rowPoly2_bound y z w) (by norm_num)
  intro i
  fin_cases i
  · simpa only [Polynomial.coeff_zero] using row2_coefficient00 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient01 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient02 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient03 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient04 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient05 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient06 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient07 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient08 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient09 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient10 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient11 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient12 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient13 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient14 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient15 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient16 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient17 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient18 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient19 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient20 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient21 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient22 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient23 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient24 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient25 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient26 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient27 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient28 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient29 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient30 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient31 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient32 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient33 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row2_coefficient34 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row2_coefficient35 y z w

#print axioms row2_identity
end SmallLevelTwentySixResultantBatchedMMM
end

section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

namespace SmallLevelTwentySixResultantBatchedMMM
open Complex Polynomial SmallLevelPolynomialCoefficientAssembly
open SmallLevelTwentySixResultantCoefficientsMMM
open scoped Classical
theorem row3_identity (y z w : ℂ) : rowPoly3 y z w=0 := by
  apply eq_of_bounded_coefficients _ _ 36
    (rowPoly3_bound y z w) (by norm_num)
  intro i
  fin_cases i
  · simpa only [Polynomial.coeff_zero] using row3_coefficient00 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient01 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient02 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient03 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient04 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient05 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient06 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient07 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient08 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient09 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient10 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient11 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient12 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient13 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient14 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient15 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient16 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient17 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient18 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient19 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient20 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient21 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient22 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient23 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient24 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient25 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient26 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient27 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient28 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient29 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient30 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient31 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient32 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row3_coefficient33 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row3_coefficient34 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row3_coefficient35 y z w

#print axioms row3_identity

theorem row4_identity (y z w : ℂ) : rowPoly4 y z w=0 := by
  apply eq_of_bounded_coefficients _ _ 36
    (rowPoly4_bound y z w) (by norm_num)
  intro i
  fin_cases i
  · simpa only [Polynomial.coeff_zero] using row4_coefficient00 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient01 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient02 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient03 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient04 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient05 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient06 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient07 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient08 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient09 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient10 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient11 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient12 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient13 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient14 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient15 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient16 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient17 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient18 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient19 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient20 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient21 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient22 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient23 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient24 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient25 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient26 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient27 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient28 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient29 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient30 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row4_coefficient31 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row4_coefficient32 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row4_coefficient33 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row4_coefficient34 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient35 y z w

#print axioms row4_identity

theorem row5_identity (y z w : ℂ) : rowPoly5 y z w=0 := by
  apply eq_of_bounded_coefficients _ _ 36
    (rowPoly5_bound y z w) (by norm_num)
  intro i
  fin_cases i
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row5_coefficient00 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient01 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient02 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient03 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient04 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient05 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient06 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient07 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient08 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient09 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient10 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient11 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient12 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient13 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient14 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient15 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient16 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient17 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient18 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient19 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient20 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient21 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient22 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient23 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient24 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient25 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient26 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient27 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient28 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient29 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row5_coefficient30 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row5_coefficient31 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row5_coefficient32 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row5_coefficient33 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row5_coefficient34 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row5_coefficient35 y z w

#print axioms row5_identity

theorem row6_identity (y z w : ℂ) : rowPoly6 y z w=0 := by
  apply eq_of_bounded_coefficients _ _ 36
    (rowPoly6_bound y z w) (by norm_num)
  intro i
  fin_cases i
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row6_coefficient00 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient01 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient02 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient03 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient04 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient05 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient06 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient07 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient08 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient09 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient10 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient11 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient12 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient13 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient14 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient15 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient16 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient17 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient18 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient19 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient20 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient21 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient22 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient23 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient24 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient25 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient26 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient27 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient28 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row6_coefficient29 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row6_coefficient30 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row6_coefficient31 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row6_coefficient32 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row6_coefficient33 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row6_coefficient34 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row6_coefficient35 y z w

#print axioms row6_identity
end SmallLevelTwentySixResultantBatchedMMM
end
end
end

/-! ## SmallLevelTwentySixResultantBatchedMMMCompleteV1 -/
section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
@[expose] public noncomputable section
namespace SmallLevelTwentySixResultantBatchedMMM
open Complex QuantitativeArithmeticSparsePolynomialCertificate
open SmallLevelTwentySixResultantCoefficientsMMM

theorem resultant_zero (x y z w a : ℂ)
    (hr : SmallLevelTwentySixUnitMMM.WeightResultants.r x y z w a 0 0=0)
    (hv : SmallLevelTwentySixUnitMMM.WeightResultants.v x y z w a 0 0=0) :
    eval x y z w 1 SmallLevelTwentySixWeightAbelMMM.terms=0 := by
  have h0 := congrArg (Polynomial.eval x) (row0_identity y z w)
  simp only [rowPoly0,Polynomial.eval_add,Polynomial.eval_mul] at h0
  have h1 := congrArg (Polynomial.eval x) (row1_identity y z w)
  simp only [rowPoly1,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_zero] at h1
  have h2 := congrArg (Polynomial.eval x) (row2_identity y z w)
  simp only [rowPoly2,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_zero] at h2
  have h3 := congrArg (Polynomial.eval x) (row3_identity y z w)
  simp only [rowPoly3,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_zero] at h3
  have h4 := congrArg (Polynomial.eval x) (row4_identity y z w)
  simp only [rowPoly4,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_zero] at h4
  have h5 := congrArg (Polynomial.eval x) (row5_identity y z w)
  simp only [rowPoly5,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_zero] at h5
  have h6 := congrArg (Polynomial.eval x) (row6_identity y z w)
  simp only [rowPoly6,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_zero] at h6
  have hd := SmallLevelCubicQuarticSylvester.resultant_zero
    ((rPoly0 y z w).eval x) ((rPoly1 y z w).eval x) ((rPoly2 y z w).eval x) ((rPoly3 y z w).eval x)
    ((vPoly0 y z w).eval x) ((vPoly1 y z w).eval x) ((vPoly2 y z w).eval x) ((vPoly3 y z w).eval x)
    ((vPoly4 y z w).eval x) ((qPoly0 y z w).eval x) ((qPoly1 y z w).eval x) ((qPoly2 y z w).eval x)
    ((qPoly3 y z w).eval x) ((qPoly4 y z w).eval x) ((qPoly5 y z w).eval x) ((qPoly6 y z w).eval x)
    ((dPoly0 y z w).eval x) a
    h0 h1 h2 h3 h4 h5 h6
    ((r_evaluation x y z w a).trans hr) ((v_evaluation x y z w a).trans hv)
  rw [d_eval_eq_abel] at hd
  exact hd

#print axioms resultant_zero
end SmallLevelTwentySixResultantBatchedMMM
end
end

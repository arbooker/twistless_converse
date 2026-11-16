module

public import QuantitativeArithmeticSparsePolynomialCertificateTheoryV4
public import SmallLevelPolynomialCoefficientAssemblyV1
public import SmallLevelSparseCoefficientAssemblyV1
public import SmallLevelSparseCoefficientPartitionV1
public import SmallLevelTwentySixUnitMMPWeightResultantsTheoryV4
public import SmallLevelTwentySixWeightAbelMMPDataV1
public import SmallLevelTwentySixResultantMMPDataV6
public import SmallLevelTwentySixResultantMMPSlices0V6
public import SmallLevelTwentySixResultantMMPSlices1V6
public import SmallLevelTwentySixResultantMMPSlices2V6
public meta import QuantitativeArithmeticSparseCertificateComputeV5
public meta import SmallLevelCertificateBatchCommandV1
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
certificate_batch {
/-! ## SmallLevelTwentySixResultantCoefficientsMMPTheoryV4 -/
section
/-! Consolidated chapter: SmallLevelTwentySixResultantCoefficientsMMP. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixResultantCoefficientsMMPAbelBridgeV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option maxHeartbeats 5000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixResultantCoefficientsMMP
open Complex QuantitativeArithmeticSparsePolynomialCertificate
open SmallLevelSparseCoefficientPartition SmallLevelSparsePolynomialNormalize
theorem abel_bounded : bounded 36 SmallLevelTwentySixWeightAbelMMP.terms=true := by bounded_sparse_data

theorem coefficient_slice_eval (y z w : ℂ) (i : Fin 36) :
    eval y z w 1 1 (slice i SmallLevelTwentySixWeightAbelMMP.terms)=eval y z w 1 1 (coefficientData i) := by
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
    (dPoly0 y z w).eval x=eval x y z w 1 SmallLevelTwentySixWeightAbelMMP.terms := by
  have hp := eval_partition 36 SmallLevelTwentySixWeightAbelMMP.terms abel_bounded x y z w
  have hd := SmallLevelSparseCoefficientAssembly.assemble_eval_polynomial coefficientData x y z w 1
  rw [coefficient_polynomial] at hd
  calc
    (dPoly0 y z w).eval x=eval x y z w 1 (SmallLevelSparseCoefficientAssembly.assemble coefficientData) := hd.symm
    _=∑ i : Fin 36,x^(i:ℕ)*eval y z w 1 1 (coefficientData i) :=
      SmallLevelSparseCoefficientAssembly.eval_assemble coefficientData x y z w 1
    _=∑ i : Fin 36,x^(i:ℕ)*eval y z w 1 1 (slice i SmallLevelTwentySixWeightAbelMMP.terms) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [coefficient_slice_eval]
    _=eval x y z w 1 SmallLevelTwentySixWeightAbelMMP.terms := hp.symm

#print axioms d_eval_eq_abel
end SmallLevelTwentySixResultantCoefficientsMMP
end
end

/-! ## SmallLevelTwentySixResultantCoefficientsMMPBoundsV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelTwentySixResultantCoefficientsMMP
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

#print axioms rowPoly0_bound
#print axioms rowPoly6_bound
end SmallLevelTwentySixResultantCoefficientsMMP
end
end

/-! ## SmallLevelTwentySixResultantCoefficientsMMPOriginalBridgeV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentySixResultantCoefficientsMMP
open Complex
open scoped Classical

theorem r_evaluation (x y z w a : ℂ) :
    (rPoly0 y z w).eval x + (rPoly1 y z w).eval x*a + (rPoly2 y z w).eval x*a^2 + (rPoly3 y z w).eval x*a^3=SmallLevelTwentySixUnitMMP.WeightResultants.r x y z w a 0 0 := by
  norm_num [rPoly0,rPoly1,rPoly2,rPoly3,r0000Block00,r0000Data,r0000,r0001Block00,r0001Data,r0001,r0002Block00,r0002Data,r0002,r0003Block00,r0003Data,r0003,r0005Block00,r0005Data,r0005,r0100Block00,r0100Data,r0100,r0101Block00,r0101Data,r0101,r0102Block00,r0102Data,r0102,r0103Block00,r0103Data,r0103,r0200Block00,r0200Data,r0200,r0201Block00,r0201Data,r0201,r0202Block00,r0202Data,r0202,r0300Block00,r0300Data,r0300,r0301Block00,r0301Data,r0301,Polynomial.ofFn_eq_sum_monomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial,Fin.sum_univ_succ,QuantitativeArithmeticSparsePolynomialCertificate.eval,QuantitativeArithmeticSparsePolynomialCertificate.monomial,SmallLevelTwentySixUnitMMP.WeightResultants.r] <;> ring

#print axioms r_evaluation

theorem v_evaluation (x y z w a : ℂ) :
    (vPoly0 y z w).eval x + (vPoly1 y z w).eval x*a + (vPoly2 y z w).eval x*a^2 + (vPoly3 y z w).eval x*a^3 + (vPoly4 y z w).eval x*a^4=SmallLevelTwentySixUnitMMP.WeightResultants.v x y z w a 0 0 := by
  norm_num [vPoly0,vPoly1,vPoly2,vPoly3,vPoly4,v0000Block00,v0000Data,v0000,v0001Block00,v0001Data,v0001,v0002Block00,v0002Data,v0002,v0003Block00,v0003Data,v0003,v0004Block00,v0004Data,v0004,v0005Block00,v0005Data,v0005,v0006Block00,v0006Data,v0006,v0007Block00,v0007Data,v0007,v0008Block00,v0008Data,v0008,v0009Block00,v0009Data,v0009,v0010Block00,v0010Data,v0010,v0011Block00,v0011Data,v0011,v0100Block00,v0100Data,v0100,v0101Block00,v0101Data,v0101,v0102Block00,v0102Data,v0102,v0103Block00,v0103Data,v0103,v0104Block00,v0104Data,v0104,v0105Block00,v0105Data,v0105,v0106Block00,v0106Data,v0106,v0107Block00,v0107Data,v0107,v0108Block00,v0108Data,v0108,v0109Block00,v0109Data,v0109,v0110Block00,v0110Data,v0110,v0200Block00,v0200Data,v0200,v0201Block00,v0201Data,v0201,v0202Block00,v0202Data,v0202,v0203Block00,v0203Data,v0203,v0204Block00,v0204Data,v0204,v0205Block00,v0205Data,v0205,v0206Block00,v0206Data,v0206,v0207Block00,v0207Data,v0207,v0208Block00,v0208Data,v0208,v0301Block00,v0301Data,v0301,v0302Block00,v0302Data,v0302,v0303Block00,v0303Data,v0303,v0304Block00,v0304Data,v0304,v0305Block00,v0305Data,v0305,v0306Block00,v0306Data,v0306,v0307Block00,v0307Data,v0307,v0401Block00,v0401Data,v0401,v0402Block00,v0402Data,v0402,v0403Block00,v0403Data,v0403,v0404Block00,v0404Data,v0404,v0405Block00,v0405Data,v0405,v0406Block00,v0406Data,v0406,Polynomial.ofFn_eq_sum_monomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial,Fin.sum_univ_succ,QuantitativeArithmeticSparsePolynomialCertificate.eval,QuantitativeArithmeticSparsePolynomialCertificate.monomial,SmallLevelTwentySixUnitMMP.WeightResultants.v] <;> ring

#print axioms v_evaluation

end SmallLevelTwentySixResultantCoefficientsMMP
end
end
end

}

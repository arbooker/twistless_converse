module

public import QuantitativeMaassDisplacementSublevelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open scoped Topology MatrixGroups

namespace QuantitativeMaass

/-- At every centre, not only i, the actual denominator is bounded by the
hyperbolic displacement. -/
theorem integral_denominator_sq_le_exp (A : SL(2,ℤ)) (z : ℍ) :
    Complex.normSq (denom (A : GL (Fin 2) ℝ) z)≤Real.exp (dist (A•z) z) := by
  have hp : 0<Complex.normSq (denom (A : GL (Fin 2) ℝ) z) := normSq_denom_pos _ z.im_ne_zero
  have h := im_le_im_mul_exp_dist z (A•z)
  rw [ModularGroup.im_smul_eq_div_normSq] at h
  rw [dist_comm z (A•z),div_mul_eq_mul_div] at h
  have hh := (le_div_iff₀ hp).mp h
  nlinarith [z.im_pos]

/-- The lower-left integral entry times height is bounded by half the
exponential displacement. This is the sharp cusp dependence. -/
theorem integral_lowerleft_height_le (A : SL(2,ℤ)) (z : ℍ) (R : ℝ)
    (hR : dist (A•z) z≤R) :
    |(A 1 0:ℝ)| * z.im≤Real.exp (R/2) := by
  have hsq : ((A 1 0:ℝ)*z.im)^2≤Real.exp R :=
    (c_mul_im_sq_le_normSq_denom (A : GL (Fin 2) ℝ) z).trans
      ((integral_denominator_sq_le_exp A z).trans (Real.exp_le_exp.mpr hR))
  have hex : (Real.exp (R/2))^2=Real.exp R := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have ha : (|(A 1 0:ℝ)| *z.im)^2=((A 1 0:ℝ)*z.im)^2 := by rw [mul_pow,sq_abs,mul_pow]
  nlinarith [Real.exp_pos (R/2),mul_nonneg (abs_nonneg (A 1 0:ℝ)) z.im_pos.le]

/-- Above a fixed propagation height, every returning integral transformation
is upper triangular. No compact-core bound depending on the height is needed. -/
theorem integral_high_cusp_lowerleft_zero (A : SL(2,ℤ)) (z : ℍ) (R : ℝ)
    (hR : dist (A•z) z≤R) (hz : Real.exp (R/2)<z.im) : A 1 0=0 := by
  by_contra hn
  have hab : (1:ℝ)≤|(A 1 0:ℝ)| := by
    have hh : (1:ℤ)≤|A 1 0| := by
      have hp : (0:ℤ) < |A 1 0| := abs_pos.mpr hn
      omega
    exact_mod_cast hh
  have hb := integral_lowerleft_height_le A z R hR
  have hh := mul_le_mul_of_nonneg_right hab z.im_pos.le
  linarith

/-- An upper-triangular unimodular integer matrix has diagonal entries
both equal to one or both equal to minus one. -/
theorem integral_upper_triangular_diagonal (A : SL(2,ℤ)) (hc : A 1 0=0) :
    (A 0 0=1 ∧ A 1 1=1) ∨ (A 0 0= -1 ∧ A 1 1= -1) := by
  have hd : A 0 0*A 1 1=1 := by
    have hh := A.property
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using hh
  exact Int.eq_one_or_neg_one_of_mul_eq_one' hd

/-- The remaining parabolic displacement is exactly the absolute upper-right
entry, measured in the Euclidean cusp coordinate. -/
theorem integral_upper_triangular_displacement (A : SL(2,ℤ)) (hc : A 1 0=0) (z : ℍ) :
    dist ((A•z:ℍ):ℂ) (z:ℂ)=|(A 0 1:ℝ)| := by
  rw [dist_eq_norm,coe_specialLinearGroup_apply]
  rcases integral_upper_triangular_diagonal A hc with ⟨ha,hd⟩ | ⟨ha,hd⟩
  · simp [hc,ha,hd]
  · simp [hc,ha,hd,div_neg,neg_add_rev,sub_eq_add_neg,add_assoc]

/-- Every high-cusp near-return has upper-right entry at most a constant
 times height; this is the linear bound needed for the sharp cusp count. -/
theorem integral_high_cusp_upperright_bound (A : SL(2,ℤ)) (z : ℍ) (R : ℝ)
    (hR : dist (A•z) z≤R) (hz : Real.exp (R/2)<z.im) :
    |(A 0 1:ℝ)|≤z.im*(Real.exp R-1) := by
  have hc := integral_high_cusp_lowerleft_zero A z R hR hz
  rw [← integral_upper_triangular_displacement A hc z]
  exact (dist_coe_le (A•z) z).trans
    (mul_le_mul_of_nonneg_left (sub_le_sub_right (Real.exp_le_exp.mpr hR) 1) z.im_pos.le)

#print axioms integral_denominator_sq_le_exp
#print axioms integral_lowerleft_height_le
#print axioms integral_high_cusp_lowerleft_zero

#print axioms integral_upper_triangular_diagonal
#print axioms integral_upper_triangular_displacement
#print axioms integral_high_cusp_upperright_bound

end QuantitativeMaass

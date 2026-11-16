module

public import QuantitativeMaassCuspConjugateCountV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open scoped Topology MatrixGroups

namespace QuantitativeMaass

/-- Integral upper-triangular transformations preserve cusp height. -/
theorem integral_upper_triangular_im (A : SL(2,ℤ)) (hc : A 1 0=0) (z : ℍ) :
    (A•z).im=z.im := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  rcases integral_upper_triangular_diagonal A hc with ⟨ha,hd⟩ | ⟨ha,hd⟩
  · simp [denom,hc,hd]
  · simp [denom,hc,hd]

/-- The nonzero parabolic translation parameter gives a quantitative lower
bound for hyperbolic displacement at every height. -/
theorem integral_upper_triangular_sinh_height (A : SL(2,ℤ)) (hc : A 1 0=0) (z : ℍ) :
    |(A 0 1:ℝ)|≤Real.sinh (dist (A•z) z)*z.im := by
  have hh := sinh_half_dist (A•z) z
  rw [integral_upper_triangular_im A hc z,integral_upper_triangular_displacement A hc z,
    ← sq,Real.sqrt_sq z.im_pos.le] at hh
  have he : Real.sinh (dist (A•z) z)=
      2*Real.sinh (dist (A•z) z/2)*Real.cosh (dist (A•z) z/2) := by
    simpa only [show 2*(dist (A•z) z/2)=dist (A•z) z by ring] using
      Real.sinh_two_mul (dist (A•z) z/2)
  rw [he,hh]
  have hid : 2*(|(A 0 1:ℝ)| /(2*z.im))*Real.cosh (dist (A•z) z/2)*z.im=
      |(A 0 1:ℝ)| *Real.cosh (dist (A•z) z/2) := by field_simp
  rw [hid]
  exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_cosh _)

/-- A nonidentity high-cusp projective return has a nonzero integral
translation parameter; scalar representatives have already been excluded. -/
theorem congruence_high_cusp_upperright_ne_zero (N : ℕ) (g : gamma N) (hg : g≠1)
    (z : ℍ) (R : ℝ) (hd : dist (g•z) z≤R) (hz : Real.exp (R/2)<z.im) :
    (representative g) 0 1≠0 := by
  have he : representative g•z=g•z := by
    rw [← integralLabel_action,representative_label]
    rfl
  have hc := integral_high_cusp_lowerleft_zero (representative g) z R (he ▸ hd) hz
  have hdiag : (representative g) 1 1=(representative g) 0 0 := by
    rcases integral_upper_triangular_diagonal (representative g) hc with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> omega
  rcases congruence_representative_nonscalar N g hg with h | h | h
  · exact False.elim (h hc)
  · exact False.elim (h hdiag)
  · exact h

/-- Every genuine nonidentity short return high in a cusp satisfies
sinh(displacement)*height >=1, with no freeness premise. -/
theorem congruence_high_cusp_sinh_height (N : ℕ) (g : gamma N) (hg : g≠1)
    (z : ℍ) (R : ℝ) (hd : dist (g•z) z≤R) (hz : Real.exp (R/2)<z.im) :
    1≤Real.sinh (dist (g•z) z)*z.im := by
  have he : representative g•z=g•z := by
    rw [← integralLabel_action,representative_label]
    rfl
  have hc := integral_high_cusp_lowerleft_zero (representative g) z R (he ▸ hd) hz
  have hn := congruence_high_cusp_upperright_ne_zero N g hg z R hd hz
  have hb : (1:ℝ)≤|((representative g) 0 1:ℝ)| := by
    have hp : (0:ℤ) < |(representative g) 0 1| := abs_pos.mpr hn
    have hh : (1:ℤ)≤|(representative g) 0 1| := by omega
    exact_mod_cast hh
  have hh := integral_upper_triangular_sinh_height (representative g) hc z
  rw [he] at hh
  exact hb.trans hh

/-- The singular factor in the checked off-diagonal kernel is bounded by
sqrt(height) for every high-cusp nonidentity return. -/
theorem congruence_high_cusp_singular_weight (N : ℕ) (g : gamma N) (hg : g≠1)
    (z : ℍ) (R : ℝ) (hd : dist (g•z) z≤R) (hz : Real.exp (R/2)<z.im) :
    0<dist (g•z) z ∧ 1/Real.sqrt (Real.sinh (dist (g•z) z))≤Real.sqrt z.im := by
  have hh := congruence_high_cusp_sinh_height N g hg z R hd hz
  have hs : 0<Real.sinh (dist (g•z) z) := by nlinarith [z.im_pos]
  refine ⟨Real.sinh_pos_iff.mp hs,?_⟩
  have ht := Real.sqrt_le_sqrt hh
  rw [Real.sqrt_one,Real.sqrt_mul hs.le] at ht
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hs)).mpr
  simpa only [mul_comm] using ht

#print axioms integral_upper_triangular_im
#print axioms integral_upper_triangular_sinh_height
#print axioms congruence_high_cusp_upperright_ne_zero
#print axioms congruence_high_cusp_sinh_height
#print axioms congruence_high_cusp_singular_weight

end QuantitativeMaass

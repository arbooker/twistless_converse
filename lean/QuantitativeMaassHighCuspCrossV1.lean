module

public import QuantitativeMaassCuspConjugateCountV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels QuantitativeSpectralObservability
open scoped Topology MatrixGroups

namespace QuantitativeMaass

/-- The denominator estimate also holds between distinct points at equal height. -/
theorem integral_cross_denominator_sq_le_exp (A : SL(2,ℤ)) (z w : ℍ)
    (hheight : z.im=w.im) :
    Complex.normSq (denom (A : GL (Fin 2) ℝ) z)≤Real.exp (dist (A•z) w) := by
  have hp : 0<Complex.normSq (denom (A : GL (Fin 2) ℝ) z) := normSq_denom_pos _ z.im_ne_zero
  have h := im_le_im_mul_exp_dist w (A•z)
  rw [ModularGroup.im_smul_eq_div_normSq,←hheight,dist_comm w (A•z),
    div_mul_eq_mul_div] at h
  have hh := (le_div_iff₀ hp).mp h
  nlinarith [z.im_pos]

theorem integral_cross_lowerleft_height_le (A : SL(2,ℤ)) (z w : ℍ)
    (hheight : z.im=w.im) (R : ℝ) (hR : dist (A•z) w≤R) :
    |(A 1 0:ℝ)| *z.im≤Real.exp (R/2) := by
  have hsq : ((A 1 0:ℝ)*z.im)^2≤Real.exp R :=
    (c_mul_im_sq_le_normSq_denom (A : GL (Fin 2) ℝ) z).trans
      ((integral_cross_denominator_sq_le_exp A z w hheight).trans (Real.exp_le_exp.mpr hR))
  have hex : (Real.exp (R/2))^2=Real.exp R := by
    rw [←Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have ha : (|(A 1 0:ℝ)| *z.im)^2=((A 1 0:ℝ)*z.im)^2 := by rw [mul_pow,sq_abs,mul_pow]
  nlinarith [Real.exp_pos (R/2),mul_nonneg (abs_nonneg (A 1 0:ℝ)) z.im_pos.le]

/-- High-cusp cross kernels on a horocycle contain only parabolic returns. -/
theorem integral_high_cusp_cross_lowerleft_zero (A : SL(2,ℤ)) (z w : ℍ)
    (hheight : z.im=w.im) (R : ℝ) (hR : dist (A•z) w≤R)
    (hz : Real.exp (R/2)<z.im) : A 1 0=0 := by
  by_contra hn
  have hab : (1:ℝ)≤|(A 1 0:ℝ)| := by
    have hh : (1:ℤ)≤|A 1 0| := by
      have hp : (0:ℤ)< |A 1 0| := abs_pos.mpr hn
      omega
    exact_mod_cast hh
  have hb := integral_cross_lowerleft_height_le A z w hheight R hR
  have hh := mul_le_mul_of_nonneg_right hab z.im_pos.le
  linarith

/-- Actual conjugation transports arbitrary pairs of kernel centers. -/
theorem cuspConjugateFull_cross_displacement (N : ℕ) (A : SL(2,ℤ))
    (g : gamma N) (z w : ℍ) :
    dist (cuspConjugateFull N A g•z) w=dist (g•(A•z)) (A•w) := by
  have he : cuspConjugateFull N A g•z=A⁻¹•(g•(A•z)) := by
    change ((integralLabel A)⁻¹*g.val*integralLabel A)•z=_
    rw [mul_smul,mul_smul,←map_inv,integralLabel_action,integralLabel_action]
    rfl
  rw [he]
  calc
    _ = dist (A⁻¹•(g•(A•z))) (A⁻¹•(A•w)) := by rw [inv_smul_smul]
    _ = _ := integral_action_dist A⁻¹ (g•(A•z)) (A•w)

#print axioms integral_cross_denominator_sq_le_exp
#print axioms integral_cross_lowerleft_height_le
#print axioms integral_high_cusp_cross_lowerleft_zero
#print axioms cuspConjugateFull_cross_displacement

end QuantitativeMaass

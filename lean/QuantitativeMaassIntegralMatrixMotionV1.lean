module

public import QuantitativeMaassMatrixMotionV1
public import QuantitativeMaassCorrespondenceWindowV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane Matrix
open scoped Topology

namespace QuantitativeMaass

/-- Positive determinant gives the same displacement numerator identity. -/
theorem positiveMatrix_displacement_identity (M : GL (Fin 2) ℝ)
    (hM : 0<M.det.val) (z : ℍ) :
    ((z:ℂ)-((M•z:ℍ):ℂ))*denom M z=realMatrixDisplacementNumerator M.val z := by
  rw [coe_smul_of_det_pos hM,sub_mul,div_mul_cancel₀ _ (denom_ne_zero _ _)]
  change (z:ℂ)*((M.val 1 0:ℂ)*(z:ℂ)+M.val 1 1)-((M.val 0 0:ℂ)*(z:ℂ)+M.val 0 1)=_
  unfold realMatrixDisplacementNumerator
  ring

/-- Determinant at least one only improves the displacement bound. -/
theorem positiveMatrix_dist_le_arsinh (M : GL (Fin 2) ℝ)
    (hM : 1≤M.det.val) (z : ℍ) :
    dist (M•z) z≤2*Real.arsinh (‖realMatrixDisplacementNumerator M.val z‖/(2*z.im)) := by
  have hd : 0<‖denom M z‖ := norm_pos_iff.mpr (denom_ne_zero _ _)
  have hp : 0<M.det.val := lt_of_lt_of_le zero_lt_one hM
  have him : z.im/‖denom M z‖^2≤(M•z).im := by
    rw [im_smul_eq_div_normSq,abs_of_pos hp,Complex.normSq_eq_norm_sq]
    exact div_le_div_of_nonneg_right (by nlinarith only [hM,z.im_pos]) (sq_nonneg _)
  have hs0 : Real.sqrt ((z.im/‖denom M z‖^2)*z.im)=z.im/‖denom M z‖ := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    ring
  have hs : z.im/‖denom M z‖≤Real.sqrt ((M•z).im*z.im) := by
    rw [←hs0]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right him z.im_pos.le)
  have hn := congrArg norm (positiveMatrix_displacement_identity M hp z)
  rw [norm_mul] at hn
  rw [UpperHalfPlane.dist_eq,dist_eq_norm,norm_sub_rev]
  apply mul_le_mul_of_nonneg_left (Real.arsinh_le_arsinh.mpr ?_) (by norm_num)
  calc
    _ ≤ ‖(z:ℂ)-((M•z:ℍ):ℂ)‖/(2*(z.im/‖denom M z‖)) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left hs (by norm_num))
    _ = _ := by rw [←hn];field_simp [z.im_ne_zero,hd.ne']

/-- A uniform logarithmic displacement bound for every positive integral
matrix; the constant does not depend on its determinant or entries. -/
theorem positiveIntegralGL_dist_log_bound (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : 0<M.det) (B : ℝ) (hB : 0≤B) (hm : ∀ i j,|(M i j:ℝ)|≤B) (z : ℍ) :
    dist (positiveIntegralGL M hM•z) z≤2*Real.log (1+B*(‖(z:ℂ)‖+1)^2/z.im) := by
  have hd : 1≤(positiveIntegralGL M hM).det.val := by
    rw [positiveIntegralGL_det]
    exact_mod_cast hM
  have he : ∀ i j,|(positiveIntegralGL M hM).val i j|≤B := hm
  calc
    _ ≤ 2*Real.arsinh (‖realMatrixDisplacementNumerator (positiveIntegralGL M hM).val z‖/(2*z.im)) :=
      positiveMatrix_dist_le_arsinh _ hd z
    _ ≤ 2*Real.arsinh ((B*(‖(z:ℂ)‖+1)^2)/(2*z.im)) :=
      mul_le_mul_of_nonneg_left (Real.arsinh_le_arsinh.mpr
        (div_le_div_of_nonneg_right (realMatrix_displacement_numerator_bound _ B hB he z) (by positivity))) (by norm_num)
    _ ≤ 2*Real.log (1+2*((B*(‖(z:ℂ)‖+1)^2)/(2*z.im))) :=
      mul_le_mul_of_nonneg_left (arsinh_le_log_one_add_two _ (by positivity)) (by norm_num)
    _ = _ := by congr 2;ring

#print axioms positiveMatrix_displacement_identity
#print axioms positiveMatrix_dist_le_arsinh
#print axioms positiveIntegralGL_dist_log_bound

end QuantitativeMaass

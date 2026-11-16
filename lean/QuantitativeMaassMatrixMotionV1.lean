module

public import QuantitativeMaassAveragingLogCostV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane Matrix
open scoped Topology

namespace QuantitativeMaass

/-- Exact displacement numerator for a determinant-one real matrix. -/
theorem realMatrix_displacement_identity (M : GL (Fin 2) ℝ) (hM : M.val.det=1) (z : ℍ) :
    ((z:ℂ)-((M•z:ℍ):ℂ))*denom M z=realMatrixDisplacementNumerator M.val z := by
  have hp : 0<M.det.val := by change 0<M.val.det;rw [hM];norm_num
  rw [coe_smul_of_det_pos hp,sub_mul,div_mul_cancel₀ _ (denom_ne_zero _ _)]
  change (z:ℂ)*((M.val 1 0:ℂ)*(z:ℂ)+M.val 1 1)-((M.val 0 0:ℂ)*(z:ℂ)+M.val 0 1)=_
  unfold realMatrixDisplacementNumerator
  ring

/-- The denominator cancels exactly from the hyperbolic displacement formula. -/
theorem realMatrix_dist_eq_arsinh (M : GL (Fin 2) ℝ) (hM : M.val.det=1) (z : ℍ) :
    dist (M•z) z=2*Real.arsinh (‖realMatrixDisplacementNumerator M.val z‖/(2*z.im)) := by
  have hd : 0<‖denom M z‖ := norm_pos_iff.mpr (denom_ne_zero _ _)
  have him : (M•z).im=z.im/‖denom M z‖^2 := by
    rw [im_smul_eq_div_normSq]
    have hh : M.det.val=1 := hM
    rw [hh,abs_one,one_mul,Complex.normSq_eq_norm_sq]
  have hs : Real.sqrt ((M•z).im*z.im)=z.im/‖denom M z‖ := by
    rw [him]
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    ring
  have hn := congrArg norm (realMatrix_displacement_identity M hM z)
  rw [norm_mul] at hn
  rw [UpperHalfPlane.dist_eq,hs,dist_eq_norm,norm_sub_rev]
  congr 2
  rw [←hn]
  field_simp [z.im_ne_zero,hd.ne']

/-- An entry bound gives a quadratic coordinate bound for the numerator. -/
theorem realMatrix_displacement_numerator_bound (M : Matrix (Fin 2) (Fin 2) ℝ)
    (B : ℝ) (_hB : 0≤B) (hm : ∀ i j,|M i j|≤B) (z : ℍ) :
    ‖realMatrixDisplacementNumerator M z‖≤B*(‖(z:ℂ)‖+1)^2 := by
  have he (i j : Fin 2) : ‖(M i j:ℂ)‖≤B := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hm i j
  have hs : ‖(M 1 1:ℂ)-(M 0 0:ℂ)‖≤2*B :=
    (norm_sub_le _ _).trans (by linarith [he 1 1,he 0 0])
  unfold realMatrixDisplacementNumerator
  calc
    _≤‖(M 1 0:ℂ)*(z:ℂ)^2‖+‖((M 1 1:ℂ)-(M 0 0:ℂ))*(z:ℂ)‖+‖(M 0 1:ℂ)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _≤B*‖(z:ℂ)‖^2+(2*B)*‖(z:ℂ)‖+B := by
      simp only [norm_mul,norm_pow]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right (he 1 0) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right hs (norm_nonneg _))) (he 0 1)
    _=_ := by ring

/-- Real determinant-one matrix displacement grows logarithmically with
its entry height, as required for long reconstruction words. -/
theorem realMatrix_dist_log_bound (M : GL (Fin 2) ℝ) (hM : M.val.det=1)
    (B : ℝ) (hB : 0≤B) (hm : ∀ i j,|M.val i j|≤B) (z : ℍ) :
    dist (M•z) z≤2*Real.log (1+B*(‖(z:ℂ)‖+1)^2/z.im) := by
  rw [realMatrix_dist_eq_arsinh M hM z]
  calc
    _≤2*Real.arsinh ((B*(‖(z:ℂ)‖+1)^2)/(2*z.im)) :=
      mul_le_mul_of_nonneg_left (Real.arsinh_le_arsinh.mpr
        (div_le_div_of_nonneg_right (realMatrix_displacement_numerator_bound M.val B hB hm z) (by positivity))) (by norm_num)
    _≤2*Real.log (1+2*((B*(‖(z:ℂ)‖+1)^2)/(2*z.im))) :=
      mul_le_mul_of_nonneg_left (arsinh_le_log_one_add_two _ (by positivity)) (by norm_num)
    _=_ := by congr 2;ring

#print axioms realMatrix_displacement_identity
#print axioms realMatrix_dist_eq_arsinh
#print axioms realMatrix_displacement_numerator_bound
#print axioms realMatrix_dist_log_bound

end QuantitativeMaass

module

public import QuantitativeMaassParabolicLineCompactV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem parabolicLineProfile_height_scale (g : ℝ → ℂ) (y v : ℝ) :
    parabolicLineProfile g y v=parabolicLineProfile g 1 (v/y) := by
  unfold parabolicLineProfile
  congr 2
  ring

theorem parabolicLineProfile_height_deriv (g : ℝ → ℂ)
    (hg : ContDiffOn ℝ ∞ g (Ici 1)) (y v : ℝ) :
    deriv (parabolicLineProfile g y) v=
      (y⁻¹:ℝ) • deriv (parabolicLineProfile g 1) (v/y) := by
  have he : parabolicLineProfile g y=fun v => parabolicLineProfile g 1 (v/y) :=
    funext (parabolicLineProfile_height_scale g y)
  have h := ((parabolicLineProfile_smooth g hg 1).differentiable (by simp)
    (v/y)).hasDerivAt.scomp v ((hasDerivAt_id v).div_const y)
  rw [he]
  simpa only [id_eq,one_div,Function.comp_def] using h.deriv

/-- Total variation of the horizontal radial profile is independent of cusp
height. This removes the height dependence before the cusp-tail integration. -/
theorem parabolicLineProfile_variation_scale (g : ℝ → ℂ)
    (hg : ContDiffOn ℝ ∞ g (Ici 1)) (y : ℝ) (hy : 0<y) :
    (∫ v,‖deriv (parabolicLineProfile g y) v‖)=
      ∫ v,‖deriv (parabolicLineProfile g 1) v‖ := by
  simp_rw [parabolicLineProfile_height_deriv g hg y,norm_smul,Real.norm_eq_abs,
    abs_inv,abs_of_pos hy]
  rw [integral_const_mul,Measure.integral_comp_div
    (fun v => ‖deriv (parabolicLineProfile g 1) v‖) y]
  simp only [abs_of_pos hy,smul_eq_mul]
  rw [←mul_assoc,inv_mul_cancel₀ hy.ne',one_mul]

#print axioms parabolicLineProfile_height_scale
#print axioms parabolicLineProfile_height_deriv
#print axioms parabolicLineProfile_variation_scale

end QuantitativeMaass

module

public import QuantitativeMaassAveragingWindowV1
public import Mathlib.Analysis.SpecialFunctions.Arsinh

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set UpperHalfPlane
open scoped Topology

namespace QuantitativeMaass

/-- A logarithmic upper bound for inverse hyperbolic sine on the positive axis. -/
theorem arsinh_le_log_one_add_two (x : ℝ) (hx : 0≤x) :
    Real.arsinh x≤Real.log (1+2*x) := by
  have hs : Real.sqrt (1+x^2)≤1+x := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  have hp : 0<x+Real.sqrt (1+x^2) := by positivity
  unfold Real.arsinh
  exact Real.log_le_log hp (by linarith)

/-- Horizontal averaging has logarithmic, rather than reciprocal, height
cost in the propagation radius. This retains polynomial matrix growth. -/
theorem averaging_translation_dist_log (z : ℍ) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    dist (u+ᵥz) z≤2*Real.log (1+1/z.im) := by
  have he : dist ((u+ᵥz:ℍ):ℂ) (z:ℂ)=|u| := by
    rw [dist_eq_norm,coe_vadd,add_sub_cancel_right,Complex.norm_real,Real.norm_eq_abs]
  rw [UpperHalfPlane.dist_eq,he,vadd_im,Real.sqrt_mul_self z.im_pos.le,abs_of_nonneg hu.1]
  have harg : u/(2*z.im)≤1/(2*z.im) := div_le_div_of_nonneg_right hu.2 (by positivity)
  calc
    _≤2*Real.arsinh (1/(2*z.im)) :=
      mul_le_mul_of_nonneg_left (Real.arsinh_le_arsinh.mpr harg) (by norm_num)
    _≤2*Real.log (1+2*(1/(2*z.im))) :=
      mul_le_mul_of_nonneg_left (arsinh_le_log_one_add_two _ (by positivity)) (by norm_num)
    _=_ := by congr 2;ring

#print axioms arsinh_le_log_one_add_two
#print axioms averaging_translation_dist_log

end QuantitativeMaass

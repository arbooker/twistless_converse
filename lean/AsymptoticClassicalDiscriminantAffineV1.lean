module

public import AsymptoticClassicalDiscriminantDecayV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalDiscriminant

open UpperHalfPlane Filter
open scoped Topology

/-- A positive affine map of the upper half-plane. -/
def affine (r : ℝ) (hr : 0 < r) (b : ℝ) (z : ℍ) : ℍ :=
  ⟨(r : ℂ) * z + b, by simpa using mul_pos hr z.im_pos⟩

@[simp] theorem affine_im (r : ℝ) (hr : 0 < r) (b : ℝ) (z : ℍ) :
    (affine r hr b z).im = r * z.im := by simp [affine]

theorem affine_tendsto (r : ℝ) (hr : 0 < r) (b : ℝ) :
    Tendsto (affine r hr b) atImInfty atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  change Tendsto (fun z : ℍ => (affine r hr b z).im) atImInfty atTop
  simpa only [Function.comp_apply, affine_im, atImInfty] using
    (tendsto_comap : Tendsto UpperHalfPlane.im atImInfty atTop).const_mul_atTop hr

/-- Positive affine changes of variable multiply Delta's exponential
 decay rate by their slope. -/
theorem log_affine_div_im_tendsto (r : ℝ) (hr : 0 < r) (b : ℝ) :
    Tendsto (fun z : ℍ => Real.log ‖ModularForm.discriminant (affine r hr b z)‖ / z.im)
      atImInfty (𝓝 ((-2 * Real.pi) * r)) := by
  have ht := (log_norm_div_im_tendsto.comp (affine_tendsto r hr b)).mul_const r
  convert ht using 1
  funext z
  simp only [Function.comp_apply, affine_im]
  field_simp [hr.ne', z.im_ne_zero]

/-- Two affine translates of Delta proportional by a nonzero constant
 must have the same slope. This is the growth input for separating cosets. -/
theorem affine_slope_eq (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (b c : ℝ)
    (a : ℂ) (ha : a ≠ 0)
    (he : ∀ z : ℍ, ModularForm.discriminant (affine r hr b z) =
      a * ModularForm.discriminant (affine s hs c z)) : r = s := by
  have hzero : Tendsto (fun z : ℍ => Real.log ‖a‖ / z.im) atImInfty (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_comap
  have hother : Tendsto
      (fun z : ℍ => Real.log ‖ModularForm.discriminant (affine r hr b z)‖ / z.im)
      atImInfty (𝓝 ((-2 * Real.pi) * s)) := by
    have ht := hzero.add (log_affine_div_im_tendsto s hs c)
    simp only [zero_add] at ht
    convert ht using 1
    funext z
    rw [he z, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr ha)
      (norm_ne_zero_iff.mpr (ModularForm.discriminant_ne_zero _)), add_div]
  have heq := tendsto_nhds_unique (log_affine_div_im_tendsto r hr b) hother
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) Real.pi_ne_zero) heq

#print axioms affine_tendsto
#print axioms log_affine_div_im_tendsto
#print axioms affine_slope_eq

end AsymptoticClassicalDiscriminant

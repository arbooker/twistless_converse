module
public import QuantitativeArithmeticSymmetricContourV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSimplePoleHorizontal
open Complex Filter FinitenessContourShift QuantitativeArithmeticSymmetricContour
open scoped Topology

theorem regular_part_horizontal_zero (F E : ℂ → ℂ) (r : ℂ) (k a b C : ℝ)
    (hab : a≤b) (he : ∀ z : ℂ,z≠(k:ℂ) → E z=F z-r/(z-(k:ℂ)))
    (hF : ∀ z : ℂ,a≤z.re → z.re≤b → 1≤|z.im| → ‖F z‖≤C/(1+z.im^2)) :
    Tendsto (horizontal E a b) atTop (𝓝 0) ∧
      Tendsto (fun T : ℝ => horizontal E a b (-T)) atTop (𝓝 0) := by
  let B : ℝ → ℝ := fun T => C/(1+T^2)+‖r‖/T
  have hB : Tendsto B atTop (𝓝 0) := by
    have hh : Tendsto (fun T : ℝ => C/(1+T^2)) atTop (𝓝 0) := by
      simpa using majorant_zero C 1
    simpa only [B,id_eq,add_zero] using hh.add (tendsto_id.const_div_atTop ‖r‖)
  have htail (z : ℂ) (T : ℝ) (hT : 1≤T) (hza : a≤z.re) (hzb : z.re≤b)
      (hi : |z.im|=T) : ‖E z‖≤B T := by
    have hT0 : 0<T := by linarith
    have hz : z≠(k:ℂ) := by
      intro h
      rw [h,ofReal_im,abs_zero] at hi
      linarith
    have hnorm : T≤‖z-(k:ℂ)‖ := by
      have hh := abs_im_le_norm (z-(k:ℂ))
      simpa only [sub_im,ofReal_im,sub_zero,hi] using hh
    have hinv : ‖(z-(k:ℂ))⁻¹‖≤1/T := by
      rw [norm_inv,one_div]
      exact inv_anti₀ hT0 hnorm
    rw [he z hz]
    apply (norm_sub_le _ _).trans
    have hsq : z.im^2=T^2 := by rw [← hi,sq_abs]
    have hf := hF z hza hzb (by rw [hi]; exact hT)
    rw [hsq] at hf
    have hr : ‖r/(z-(k:ℂ))‖≤‖r‖/T := by
      rw [div_eq_mul_inv,norm_mul]
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv (norm_nonneg r)
    exact add_le_add hf hr
  constructor
  · apply horizontal_zero_of_eventual_bound hab B hB
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    intro x hx hx'
    apply htail _ T hT (by simpa using hx) (by simpa using hx')
    simp only [add_im,ofReal_im,mul_I_im,ofReal_re,zero_add,abs_of_nonneg (by linarith : 0≤T)]
  · apply squeeze_zero_norm' _ (by simpa using hB.mul_const |b-a|)
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    apply htail _ T hT (by simpa using hx.1.le) (by simpa using hx.2)
    simp only [add_im,ofReal_im,mul_I_im,ofReal_re,zero_add,abs_neg,abs_of_nonneg (by linarith : 0≤T)]
#print axioms regular_part_horizontal_zero
end QuantitativeArithmeticSimplePoleHorizontal

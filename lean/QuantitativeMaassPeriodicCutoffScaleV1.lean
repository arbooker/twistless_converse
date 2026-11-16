module

public import QuantitativeMaassPeriodicCutoffV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- Scaling the compact partition to an actual cusp width. -/
theorem periodCutoff_integral_width (w : ℝ) (hw : 0<w)
    (F : ℝ → ℂ) (hF : Continuous F) (hp : Function.Periodic F w) :
    (∫ x in (0:ℝ)..(2*w), periodCutoff (x/w) • F x)=∫ x in (0:ℝ)..w, F x := by
  have hper : Function.Periodic (fun x => F (w*x)) 1 := by
    intro x
    simpa only [mul_add,mul_one] using hp (w*x)
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (fun x => periodCutoff (x/w) • F x) (a := (0:ℝ)) (b := 2) w
  have hs' := intervalIntegral.smul_integral_comp_mul_left F (a := (0:ℝ)) (b := 1) w
  simp only [mul_zero,mul_one,mul_div_cancel_left₀ _ hw.ne'] at hs hs'
  rw [mul_comm w 2] at hs
  rw [← hs,periodCutoff_integral (fun x => F (w*x))
    (hF.comp (continuous_const.mul continuous_id)) hper,hs']

/-- The horizontal second-derivative cancellation survives the exact cusp
width scaling. The chain-rule factor w^-2 can be pulled out separately. -/
theorem periodCutoff_second_integral_width (w : ℝ) (hw : 0<w)
    (F : ℝ → ℂ) (hF : Continuous F) (hp : Function.Periodic F w) :
    (∫ x in (0:ℝ)..(2*w), deriv (deriv periodCutoff) (x/w) • F x)=0 := by
  have hper : Function.Periodic (fun x => F (w*x)) 1 := by
    intro x
    simpa only [mul_add,mul_one] using hp (w*x)
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (fun x => deriv (deriv periodCutoff) (x/w) • F x) (a := (0:ℝ)) (b := 2) w
  simp only [mul_zero,mul_div_cancel_left₀ _ hw.ne'] at hs
  rw [mul_comm w 2] at hs
  rw [← hs,periodCutoff_second_integral (fun x => F (w*x))
    (hF.comp (continuous_const.mul continuous_id)) hper,smul_zero]

/-- Set-integral version matching the actual rectangle Fubini formula. -/
theorem periodCutoff_setIntegral_width (w : ℝ) (hw : 0<w)
    (F : ℝ → ℂ) (hF : Continuous F) (hp : Function.Periodic F w) :
    (∫ x in Icc (0:ℝ) (2*w), periodCutoff (x/w) • F x)=∫ x in Icc (0:ℝ) w, F x := by
  simpa only [intervalIntegral.integral_of_le hw.le,
    intervalIntegral.integral_of_le (show 0≤2*w by positivity),
    integral_Icc_eq_integral_Ioc] using periodCutoff_integral_width w hw F hF hp

theorem periodCutoff_second_setIntegral_width (w : ℝ) (hw : 0<w)
    (F : ℝ → ℂ) (hF : Continuous F) (hp : Function.Periodic F w) :
    (∫ x in Icc (0:ℝ) (2*w), deriv (deriv periodCutoff) (x/w) • F x)=0 := by
  simpa only [intervalIntegral.integral_of_le (show 0≤2*w by positivity),
    integral_Icc_eq_integral_Ioc] using periodCutoff_second_integral_width w hw F hF hp

#print axioms periodCutoff_setIntegral_width
#print axioms periodCutoff_second_setIntegral_width

end QuantitativeMaass

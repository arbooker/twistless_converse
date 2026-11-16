module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff

namespace QuantitativeMaass

/-- Elementary integral Cauchy--Schwarz with the interval length explicit. -/
theorem interval_integral_sq_le_length (g : ℝ → ℝ) (hg : Continuous g)
    (w : ℝ) (hw : 0<w) :
    (∫ x in (0:ℝ)..w,g x)^2 ≤ w * ∫ x in (0:ℝ)..w,(g x)^2 := by
  let I := ∫ x in (0:ℝ)..w,g x
  have hnon := intervalIntegral.integral_nonneg_of_forall (μ := volume) hw.le
    (fun x => sq_nonneg (w*g x-I))
  have he : (∫ x in (0:ℝ)..w,(w*g x-I)^2)=
      w^2*(∫ x in (0:ℝ)..w,(g x)^2)-w*I^2 := by
    have hp : (fun x => (w*g x-I)^2)=
        (fun x => w^2*(g x)^2-(2*w*I)*g x+I^2) := by funext x;ring
    rw [hp,intervalIntegral.integral_add,intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
      simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
      change w^2*(∫ x in (0:ℝ)..w,(g x)^2)-(2*w*I)*I+w*I^2=_
      ring
    · exact (continuous_const.mul (hg.pow 2)).intervalIntegrable _ _
    · exact (continuous_const.mul hg).intervalIntegrable _ _
    · exact ((continuous_const.mul (hg.pow 2)).sub
        (continuous_const.mul hg)).intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
  rw [he] at hnon
  nlinarith

theorem norm_sub_le_total_derivative (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (w : ℝ) (x y : ℝ) (hx : x∈Icc 0 w) (hy : y∈Icc 0 w) :
    ‖f x-f y‖ ≤ ∫ t in (0:ℝ)..w,‖deriv f t‖ := by
  have hd : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have hordered (a b : ℝ) (ha : a∈Icc 0 w) (hb : b∈Icc 0 w) (hab : a≤b) :
      ‖f b-f a‖ ≤ ∫ t in (0:ℝ)..w,‖deriv f t‖ := by
    apply (norm_sub_le_integral_of_norm_deriv_le_of_le hab hf.continuous.continuousOn
      (hf.differentiable (by simp)).differentiableOn
      (Eventually.of_forall (fun _ _ => le_rfl))
      (hd.norm.intervalIntegrable _ _)).trans
    exact intervalIntegral.integral_mono_interval ha.1 hab hb.2
      (Eventually.of_forall (fun _ => norm_nonneg _)) (hd.norm.intervalIntegrable _ _)
  rcases le_total x y with hxy|hyx
  · rw [norm_sub_rev]
    exact hordered x y hx hy hxy
  · exact hordered y x hy hx hyx

/-- A zero horizontal average controls each value by the horizontal
derivative. This applies to complex-valued cusp slices. -/
theorem zero_mean_norm_le_derivative_integral (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (w : ℝ) (hw : 0<w) (hm : (∫ t in (0:ℝ)..w,f t)=0)
    (x : ℝ) (hx : x∈Icc 0 w) :
    ‖f x‖ ≤ ∫ t in (0:ℝ)..w,‖deriv f t‖ := by
  have hcalc : w*‖f x‖ ≤ w*(∫ t in (0:ℝ)..w,‖deriv f t‖) := by
    calc
      _ = ‖∫ t in (0:ℝ)..w,f x-f t‖ := by
        rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
          (hf.continuous.intervalIntegrable _ _),hm,sub_zero,intervalIntegral.integral_const]
        simp [Real.norm_eq_abs,abs_of_pos hw]
      _ ≤ ∫ t in (0:ℝ)..w,‖f x-f t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hw.le
      _ ≤ ∫ _t in (0:ℝ)..w,(∫ t in (0:ℝ)..w,‖deriv f t‖) := by
        apply intervalIntegral.integral_mono_on hw.le
          ((continuous_const.sub hf.continuous).norm.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
        exact fun y hy => norm_sub_le_total_derivative f hf w x y hx hy
      _ = _ := by simp
  exact (mul_le_mul_iff_right₀ hw).mp hcalc

/-- Explicit horizontal Poincare bound for a smooth complex-valued
zero-mean slice. No periodic endpoint regularity is assumed. -/
theorem zero_mean_horizontal_energy (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (w : ℝ) (hw : 0<w) (hm : (∫ t in (0:ℝ)..w,f t)=0) :
    (∫ x in (0:ℝ)..w,‖f x‖^2) ≤ w^2*(∫ x in (0:ℝ)..w,‖deriv f x‖^2) := by
  have hd : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have hc := interval_integral_sq_le_length (fun x => ‖deriv f x‖) hd.norm w hw
  calc
    _ ≤ ∫ _x in (0:ℝ)..w,(∫ t in (0:ℝ)..w,‖deriv f t‖)^2 := by
      apply intervalIntegral.integral_mono_on hw.le
        ((hf.continuous.norm.pow 2).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)
      intro x hx
      exact pow_le_pow_left₀ (norm_nonneg _)
        (zero_mean_norm_le_derivative_integral f hf w hw hm x hx) 2
    _ = w*(∫ t in (0:ℝ)..w,‖deriv f t‖)^2 := by simp
    _ ≤ w^2*(∫ x in (0:ℝ)..w,‖deriv f x‖^2) := by
      nlinarith [mul_le_mul_of_nonneg_left hc hw.le]

#print axioms interval_integral_sq_le_length
#print axioms norm_sub_le_total_derivative
#print axioms zero_mean_norm_le_derivative_integral
#print axioms zero_mean_horizontal_energy

end QuantitativeMaass

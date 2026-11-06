module
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSimplePoleVertical
open Complex MeasureTheory Filter
open scoped Topology

def realKernel (a t : ℝ) : ℝ := a⁻¹*(1+(a⁻¹*t)^2)⁻¹

theorem realKernel_integrable (a : ℝ) (ha : a≠0) : Integrable (realKernel a) :=
  (integrable_inv_one_add_mul_sq (inv_ne_zero ha)).const_mul _

theorem realKernel_integral (a : ℝ) :
    (∫ t : ℝ,realKernel a t)=a⁻¹*(Real.pi/|a⁻¹|) := by
  change (∫ t : ℝ,a⁻¹*(1+(a⁻¹*t)^2)⁻¹)=_
  rw [integral_const_mul,integral_univ_inv_one_add_mul_sq]

theorem inverse_continuous (a : ℝ) (ha : a≠0) :
    Continuous (fun t : ℝ => ((a:ℂ)+(t:ℂ)*I)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro t ht
  apply ha
  have hh := congrArg Complex.re ht
  simpa using hh

set_option linter.unusedSimpArgs false in
theorem paired_inverse (a t : ℝ) (ha : a≠0) :
    ((a:ℂ)+(t:ℂ)*I)⁻¹+((a:ℂ)+(-t:ℂ)*I)⁻¹=2*(realKernel a t:ℂ) := by
  have hs : a^2+t^2≠0 := by nlinarith [sq_pos_of_ne_zero ha,sq_nonneg t]
  have h2re : (2:ℂ).re=2 := rfl
  have h2im : (2:ℂ).im=0 := rfl
  apply Complex.ext
  all_goals
    simp only [Complex.add_re,Complex.add_im,Complex.inv_re,Complex.inv_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,Complex.neg_re,Complex.neg_im,
      Complex.normSq_apply,realKernel]
    norm_num only
    simp only [h2re,h2im,mul_zero,mul_one,zero_mul,zero_add,add_zero,sub_zero,zero_sub,
      neg_zero,zero_pow (by decide : (2:ℕ)≠0),neg_sq]
    field_simp [ha,hs]
    ring

theorem symmetric_inverse_integral (a T : ℝ) (ha : a≠0) :
    (∫ t : ℝ in -T..T,((a:ℂ)+(t:ℂ)*I)⁻¹)=
      ((∫ t : ℝ in -T..T,realKernel a t : ℝ):ℂ) := by
  let f : ℝ → ℂ := fun t => ((a:ℂ)+(t:ℂ)*I)⁻¹
  have hf := inverse_continuous a ha
  have hfneg : Continuous (fun t : ℝ => f (-t)) := hf.comp continuous_neg
  have he : (∫ t : ℝ in -T..T,f (-t))=∫ t : ℝ in -T..T,f t := by
    rw [intervalIntegral.integral_comp_neg]
    simp only [neg_neg]
  have hsum := intervalIntegral.integral_add (hf.intervalIntegrable (μ:=volume) (-T) T)
    (hfneg.intervalIntegrable (μ:=volume) (-T) T)
  have hp : (fun t : ℝ => f t+f (-t))=(fun t : ℝ => 2*(realKernel a t:ℂ)) := by
    funext t
    simpa only [f,Complex.ofReal_neg] using paired_inverse a t ha
  rw [hp,he,intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal] at hsum
  change (∫ t : ℝ in -T..T,f t)=_
  linear_combination -hsum/2

theorem symmetric_inverse_limit (a : ℝ) (ha : a≠0) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T,((a:ℂ)+(t:ℂ)*I)⁻¹)
      atTop (𝓝 ((a⁻¹*(Real.pi/|a⁻¹|):ℝ):ℂ)) := by
  simp only [symmetric_inverse_integral a _ ha]
  have h := intervalIntegral_tendsto_integral (realKernel_integrable a ha) tendsto_neg_atTop_atBot tendsto_id
  rw [realKernel_integral] at h
  simpa only [Function.comp_def,id_eq,intervalIntegral.integral_ofReal] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp h
#print axioms symmetric_inverse_limit
end QuantitativeArithmeticSimplePoleVertical

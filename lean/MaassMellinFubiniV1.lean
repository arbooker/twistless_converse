module

public import MaassBilateralBetaV1
public import MaassBilateralKernelV1
public import Mathlib.Analysis.MellinTransform

set_option autoImplicit false

@[expose] public section

open Set MeasureTheory

namespace MaassMellin

noncomputable def doubleKernel (s ν : ℂ) (r x : ℝ) : ℂ :=
  (x:ℂ)^(s-1) * fullKernel ν x r

theorem scaled_gamma_integrable {s : ℂ} (hs : 0<s.re) {c : ℝ} (hc : 0<c) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*(Real.exp (-c*x):ℂ)) (Ioi 0) := by
  have he : MellinConvergent (fun x : ℝ => (Real.exp (-x):ℂ)) s := by
    simpa only [MellinConvergent, smul_eq_mul, mul_comm] using Complex.GammaIntegral_convergent hs
  have h := (MellinConvergent.comp_mul_left hc).mpr he
  simpa only [MellinConvergent, smul_eq_mul, neg_mul] using h

theorem doubleKernel_section_integrable {s : ℂ} (hs : 0<s.re) (ν : ℂ) (r : ℝ) :
    IntegrableOn (doubleKernel s ν r) (Ioi 0) := by
  apply ((scaled_gamma_integrable hs (Real.cosh_pos r)).mul_const
    (Complex.exp (ν*(r:ℂ)))).congr
  apply Filter.Eventually.of_forall
  intro x
  dsimp [doubleKernel, fullKernel]
  rw [show -Real.cosh r*x = -x*Real.cosh r by ring]
  ring

theorem doubleKernel_norm {s ν : ℂ} {x : ℝ} (hx : 0<x) (r : ℝ) :
    ‖doubleKernel s ν r x‖ =
      (x^(s.re-1)*Real.exp (-(Real.cosh r*x))) * Real.exp (ν.re*r) := by
  simp only [doubleKernel, fullKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.sub_re, Complex.one_re, Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [show -x*Real.cosh r = -(Real.cosh r*x) by ring]
  ring

theorem doubleKernel_norm_integral {s ν : ℂ} (hs : 0<s.re) (r : ℝ) :
    (∫ x in Ioi (0:ℝ), ‖doubleKernel s ν r x‖) =
      Real.Gamma s.re * ‖bilateral (s.re:ℂ) (ν.re:ℂ) r‖ := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => doubleKernel_norm hx r),
    integral_mul_const, Real.integral_rpow_mul_exp_neg_mul_Ioi hs (Real.cosh_pos r)]
  simp only [bilateral, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.norm_cpow_eq_rpow_re_of_pos (Real.cosh_pos r),
    Complex.neg_re]
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
  ring

/-- Absolute product integrability is proved before any Fubini exchange. -/
theorem doubleKernel_integrable {s ν : ℂ} (hs : 1<s.re) (hν : |ν.re|<s.re) :
    Integrable (Function.uncurry (doubleKernel s ν))
      (volume.prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hc : Continuous (Function.uncurry (doubleKernel s ν)) := by
    have hp := Complex.continuous_ofReal_cpow_const
      (y := s-1) (by simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr hs)
    exact (hp.comp continuous_snd).mul (by unfold fullKernel; fun_prop)
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun r => doubleKernel_section_integrable (by linarith) ν r)
  · have hb := (bilateral_integrable (s := (s.re:ℂ)) (ν := (ν.re:ℂ))
        (by simpa only [Complex.ofReal_re] using hν)).norm.const_mul (Real.Gamma s.re)
    apply hb.congr
    exact Filter.Eventually.of_forall (fun r => (doubleKernel_norm_integral (by linarith) r).symm)

theorem doubleKernel_integral {s : ℂ} (hs : 0<s.re) (ν : ℂ) (r : ℝ) :
    (∫ x in Ioi (0:ℝ), doubleKernel s ν r x) = Complex.Gamma s * bilateral s ν r := by
  have he (x:ℝ) : doubleKernel s ν r x =
      ((x:ℂ)^(s-1)*Complex.exp (-((Real.cosh r:ℂ)*(x:ℂ)))) * Complex.exp (ν*(r:ℂ)) := by
    simp only [doubleKernel, fullKernel, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
    rw [mul_comm (- (x:ℂ)) (Real.cosh r:ℂ)]
    ring
  simp_rw [he]
  rw [integral_mul_const, Complex.integral_cpow_mul_exp_neg_mul_Ioi hs (Real.cosh_pos r)]
  have hp : (1/(Real.cosh r:ℂ))^s = (Real.cosh r:ℂ)^(-s) := by
    rw [show (1/(Real.cosh r:ℂ)) = ((1/Real.cosh r:ℝ):ℂ) by push_cast; rfl,
      cpow_pos _ (by positivity) _, cpow_pos _ (Real.cosh_pos r) _,
      Real.log_div one_ne_zero (Real.cosh_pos r).ne', Real.log_one]
    congr 1
    push_cast
    ring
  rw [hp]
  unfold bilateral
  ring

#print axioms doubleKernel_integrable
#print axioms doubleKernel_integral

end MaassMellin

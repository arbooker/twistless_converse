module

public import MaassLogitV1
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Function.JacobianOneDim

set_option autoImplicit false

@[expose] public section

open Set MeasureTheory

namespace MaassMellin

noncomputable def bilateral (s ν : ℂ) (r : ℝ) : ℂ :=
  Complex.exp (ν*(r:ℂ)) * (Real.cosh r : ℂ)^(-s)

theorem cpow_pos (x : ℝ) (hx : 0<x) (z : ℂ) :
    (x:ℂ)^z = Complex.exp ((Real.log x:ℂ)*z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le]

theorem logit_jacobian_exp {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    (1/(2*u*(1-u)) : ℝ) = Real.exp (-Real.log 2 - Real.log u - Real.log (1-u)) := by
  rw [Real.exp_sub, Real.exp_sub, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<2),
    Real.exp_log hu.1, Real.exp_log (sub_pos.mpr hu.2)]
  simp only [mul_inv_rev, div_eq_mul_inv]
  ring

theorem logit_pullback (s ν : ℂ) {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    |1/(2*u*(1-u))| • bilateral s ν (logit u) =
      (2:ℂ)^(s-1) * ((u:ℂ)^((s+ν)/2-1) * (1-(u:ℂ))^((s-ν)/2-1)) := by
  have hv : 0<1-u := sub_pos.mpr hu.2
  have hu0 : 0<u := hu.1
  have htwo : (2:ℂ)^(s-1) = Complex.exp ((Real.log 2:ℂ)*(s-1)) := by
    simpa only [Complex.ofReal_ofNat] using cpow_pos 2 (by norm_num) (s-1)
  rw [abs_of_pos (by positivity : (0:ℝ)<1/(2*u*(1-u))),
    Complex.real_smul, logit_jacobian_exp hu, Complex.ofReal_exp,
    bilateral, cpow_pos _ (Real.cosh_pos _) _, log_cosh_logit hu,
    htwo, cpow_pos u hu.1 _]
  rw [show (1-(u:ℂ)) = ((1-u:ℝ):ℂ) by push_cast; rfl, cpow_pos (1-u) hv _]
  simp only [logit, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_neg, Complex.ofReal_ofNat]
  simp only [← Complex.exp_add]
  congr 1
  ring

theorem bilateral_integrable {s ν : ℂ} (hs : |ν.re| < s.re) :
    Integrable (bilateral s ν) := by
  have hA : 0<((s+ν)/2).re := by
    simp only [Complex.div_ofNat_re, Complex.add_re]
    linarith [neg_abs_le ν.re]
  have hB : 0<((s-ν)/2).re := by
    simp only [Complex.div_ofNat_re, Complex.sub_re]
    linarith [le_abs_self ν.re]
  have hb := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mp
    (Complex.betaIntegral_convergent hA hB)
  have hp : IntegrableOn (fun u : ℝ => |1/(2*u*(1-u))| • bilateral s ν (logit u)) (Ioo 0 1) := by
    apply (hb.const_mul ((2:ℂ)^(s-1))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact (logit_pullback s ν hu).symm
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun u hu => (logit_hasDerivAt hu).hasDerivWithinAt) logit_injOn (bilateral s ν)).mpr hp
  simpa only [logit_image, integrableOn_univ] using h

theorem bilateral_integral (s ν : ℂ) :
    (∫ r : ℝ, bilateral s ν r) =
      (2:ℂ)^(s-1) * Complex.betaIntegral ((s+ν)/2) ((s-ν)/2) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun u hu => (logit_hasDerivAt hu).hasDerivWithinAt) logit_injOn (bilateral s ν)
  rw [logit_image, setIntegral_univ] at h
  rw [h]
  calc
    _ = ∫ u in Ioo (0:ℝ) 1, (2:ℂ)^(s-1) *
        ((u:ℂ)^((s+ν)/2-1) * (1-(u:ℂ))^((s-ν)/2-1)) :=
      setIntegral_congr_fun measurableSet_Ioo (fun u hu => logit_pullback s ν hu)
    _ = _ := by
      rw [integral_const_mul, Complex.betaIntegral,
        intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1), integral_Ioc_eq_integral_Ioo]

#print axioms bilateral_integrable
#print axioms bilateral_integral

end MaassMellin

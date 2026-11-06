module

public import MaassSpectralKernelV1
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false

@[expose] public section

open Set MeasureTheory

namespace MaassMellin

noncomputable def fullKernel (ν : ℂ) (x r : ℝ) : ℂ :=
  (Real.exp (-x*Real.cosh r):ℂ) * Complex.exp (ν*(r:ℂ))

theorem fullKernel_neg (ν : ℂ) (x r : ℝ) : fullKernel ν x (-r) = fullKernel (-ν) x r := by
  simp only [fullKernel, Real.cosh_neg, Complex.ofReal_neg, mul_neg, neg_mul]

theorem fullKernel_half_integrable {ν : ℂ} (hν : ν.re ≤ 1) {x : ℝ} (hx : 0<x) :
    IntegrableOn (fullKernel ν x) (Ioi 0) := by
  have hm : IntegrableOn (fun r : ℝ => Real.cosh r * Real.exp (-x*Real.cosh r)) (Ioi 0) := by
    simpa only [pow_one, zero_mul, Real.cos_zero, mul_one] using
      MaassKBessel.moment_integrable 1 0 hx
  apply (hm.const_mul 2).mono'
  · exact (by unfold fullKernel; fun_prop : Continuous (fullKernel ν x)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0≤r := le_of_lt hr
    dsimp only [fullKernel]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    have he : Real.exp (ν.re*r) ≤ 2*Real.cosh r := by
      calc
        _ ≤ Real.exp r := Real.exp_le_exp.mpr (by nlinarith)
        _ ≤ _ := by rw [Real.cosh_eq]; linarith [Real.exp_pos (-r)]
    nlinarith [mul_le_mul_of_nonneg_left he (Real.exp_pos (-x*Real.cosh r)).le]

theorem fullKernel_integrable {ν : ℂ} (hν : |ν.re|≤1) {x : ℝ} (hx : 0<x) :
    Integrable (fullKernel ν x) := by
  have hp := fullKernel_half_integrable ((le_abs_self ν.re).trans hν) hx
  have hm : IntegrableOn (fun r => fullKernel ν x (-r)) (Ici (0:ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    simpa only [fullKernel_neg] using
      fullKernel_half_integrable (ν := -ν)
        (by simpa only [Complex.neg_re] using ((neg_le_abs ν.re).trans hν)) hx
  have hn : IntegrableOn (fullKernel ν x) (Iic (0:ℝ)) := by
    apply (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg volume)
      (Homeomorph.neg ℝ).measurableEmbedding).mp
    simpa only [neg_preimage, neg_Iic, neg_zero, Function.comp_def] using hm
  simpa only [Iic_union_Ioi, integrableOn_univ] using hn.union hp

theorem fullKernel_pair (ν : ℂ) (x r : ℝ) :
    fullKernel ν x (-r) + fullKernel ν x r =
      2 * ((Real.exp (-x*Real.cosh r):ℂ) * Complex.cosh (ν*(r:ℂ))) := by
  simp only [fullKernel, Real.cosh_neg, Complex.ofReal_neg, mul_neg, Complex.cosh]
  ring

theorem order_re_bound (p : MaassSpectral.Parameter) : |(MaassSpectral.order p).re| < 1/2 := by
  cases p with
  | principal r => simp [MaassSpectral.order, MaassSpectral.parameter]
  | exceptional τ hτ =>
    simpa [MaassSpectral.order, MaassSpectral.parameter, ← mul_assoc] using hτ

theorem actual_full_line (p : MaassSpectral.Parameter) {x : ℝ} (hx : 0<x) :
    (MaassSpectral.K p x:ℂ) = (1/2:ℂ) * ∫ r : ℝ, fullKernel (MaassSpectral.order p) x r := by
  have hb : |(MaassSpectral.order p).re|≤1 := le_trans (order_re_bound p).le (by norm_num)
  have hi := fullKernel_integrable hb hx
  have hn : IntegrableOn (fun r => fullKernel (MaassSpectral.order p) x (-r)) (Ioi (0:ℝ)) := by
    simpa only [fullKernel_neg] using fullKernel_half_integrable
      (ν := -MaassSpectral.order p)
        (by simpa only [Complex.neg_re] using ((neg_le_abs (MaassSpectral.order p).re).trans hb)) hx
  have heq : (∫ r : ℝ, fullKernel (MaassSpectral.order p) x r) =
      2 * ∫ r in Ioi (0:ℝ), (Real.exp (-x*Real.cosh r):ℂ) *
        Complex.cosh (MaassSpectral.order p*(r:ℂ)) := by
    rw [← intervalIntegral.integral_Iic_add_Ioi (hi.integrableOn (s := Iic (0:ℝ)))
      (hi.integrableOn (s := Ioi (0:ℝ)))]
    rw [← show (∫ r in Ioi (0:ℝ), fullKernel (MaassSpectral.order p) x (-r)) =
      ∫ r in Iic (0:ℝ), fullKernel (MaassSpectral.order p) x r by
        simpa only [neg_zero] using integral_comp_neg_Ioi 0 (fullKernel (MaassSpectral.order p) x)]
    rw [← integral_add hn hi.integrableOn]
    simp_rw [fullKernel_pair]
    rw [integral_const_mul]
  rw [heq]
  have hhalf : (1/2:ℂ)*2=1 := by norm_num
  rw [← mul_assoc, hhalf, one_mul]
  cases p with
  | principal t =>
    have hc (r:ℝ) : Complex.cosh (MaassSpectral.order (.principal t)*(r:ℂ)) =
        (Real.cos (t*r):ℂ) := by
      dsimp [MaassSpectral.order, MaassSpectral.parameter]
      rw [show Complex.I*(t:ℂ)*(r:ℂ) = ((t*r:ℝ):ℂ)*Complex.I by push_cast; ring,
        Complex.cosh_mul_I, ← Complex.ofReal_cos]
    simp_rw [hc, ← Complex.ofReal_mul]
    exact integral_complex_ofReal.symm
  | exceptional τ hτ =>
    have hc (r:ℝ) : Complex.cosh (MaassSpectral.order (.exceptional τ hτ)*(r:ℂ)) =
        (Real.cosh (τ*r):ℂ) := by
      simp only [MaassSpectral.order, MaassSpectral.parameter, ← mul_assoc,
        Complex.I_mul_I, neg_mul, Complex.cosh_neg, one_mul]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh]
    simp_rw [hc, ← Complex.ofReal_mul]
    simpa only [MaassSpectral.K, MaassExceptional.K, MaassExceptional.moment, pow_zero,
      one_mul] using (integral_complex_ofReal (f := fun r =>
        Real.exp (-x*Real.cosh r)*Real.cosh (τ*r)) (μ := volume.restrict (Ioi 0))).symm

#print axioms fullKernel_integrable
#print axioms actual_full_line

end MaassMellin

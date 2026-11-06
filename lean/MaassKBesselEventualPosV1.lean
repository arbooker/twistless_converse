module

public import MaassKBesselODEV1
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace MaassKBessel

noncomputable def sinhMoment (x : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), r * Real.sinh r * Real.exp (-x * Real.cosh r)

theorem sinhMoment_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun r : ℝ => r * Real.sinh r * Real.exp (-x * Real.cosh r)) (Ioi 0) := by
  have hg : IntegrableOn (fun r : ℝ => Real.cosh r ^ 2 * Real.exp (-x * Real.cosh r)) (Ioi 0) := by
    simpa only [zero_mul, Real.cos_zero, mul_one] using moment_integrable 2 0 hx
  apply hg.mono'
  · exact (by fun_prop : Continuous (fun r : ℝ => r * Real.sinh r *
        Real.exp (-x * Real.cosh r))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (mul_nonneg hr.le (Real.sinh_nonneg_iff.mpr hr.le)) (Real.exp_pos _).le)]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    calc
      r * Real.sinh r ≤ Real.cosh r * Real.cosh r :=
        mul_le_mul (self_le_cosh_of_nonneg hr.le) (Real.sinh_lt_cosh r).le
          (Real.sinh_nonneg_iff.mpr hr.le) (Real.cosh_pos r).le
      _ = _ := by ring

theorem r_boundary_hasDerivAt (x r : ℝ) :
    HasDerivAt (fun s : ℝ => s * Real.exp (-x * Real.cosh s))
      (Real.exp (-x * Real.cosh r) - x * (r * Real.sinh r * Real.exp (-x * Real.cosh r))) r := by
  convert (hasDerivAt_id r).mul (((Real.hasDerivAt_cosh r).const_mul (-x)).exp) using 1
  all_goals try funext s
  all_goals dsimp
  all_goals ring

theorem r_boundary_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun r : ℝ => r * Real.exp (-x * Real.cosh r)) atTop (𝓝 0) := by
  have he : Tendsto (fun r : ℝ => Real.exp (-(x/2)*r)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (by linarith : -(x/2)<0) tendsto_id)
  apply squeeze_zero_norm' _ (by simpa using he.const_mul (1/(x/2)))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  have hb : Real.cosh r * Real.exp (-x * Real.cosh r) ≤
      (1/(x/2)) * Real.exp (-(x/2)*r) := by
    simpa only [pow_one, zero_mul, Real.cos_zero, mul_one, Nat.factorial_one,
      Nat.cast_one, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos r),
      abs_of_pos (Real.exp_pos _)] using moment_majorant 1 0 hx hr
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr (Real.exp_pos _).le)]
  convert (mul_le_mul_of_nonneg_right (self_le_cosh_of_nonneg hr) (Real.exp_pos _).le).trans hb using 1
  ring

/-- Integration by parts for the actual r*sinh(r) moment. -/
theorem sinhMoment_identity {x : ℝ} (hx : 0 < x) : x * sinhMoment x = K 0 x := by
  have hi : IntegrableOn (fun r : ℝ => Real.exp (-x * Real.cosh r) -
      x * (r * Real.sinh r * Real.exp (-x * Real.cosh r))) (Ioi 0) :=
    (kernel_zero_integrable hx).sub ((sinhMoment_integrable hx).const_mul x)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun r (_ : r ∈ Ici (0 : ℝ)) => r_boundary_hasDerivAt x r) hi (r_boundary_tendsto hx)
  rw [integral_sub (kernel_zero_integrable hx) ((sinhMoment_integrable hx).const_mul x),
    integral_const_mul] at h
  simp only [zero_mul, sub_zero] at h
  have hk : (∫ r in Ioi (0:ℝ), Real.exp (-x * Real.cosh r)) = K 0 x := by simp [K]
  rw [hk] at h
  change K 0 x - x * sinhMoment x = 0 at h
  linarith

theorem K_lower_integral (t : ℝ) {x : ℝ} (hx : 0 < x) :
    K 0 x - (t^2/2) * sinhMoment x ≤ K t x := by
  have hi : IntegrableOn (fun r : ℝ => Real.exp (-x * Real.cosh r) -
      (t^2/2) * (r * Real.sinh r * Real.exp (-x * Real.cosh r))) (Ioi 0) :=
    (kernel_zero_integrable hx).sub ((sinhMoment_integrable hx).const_mul (t^2/2))
  have h := integral_mono_ae hi (kernel_integrable t hx) (show ∀ᵐ r ∂volume.restrict (Ioi (0:ℝ)),
      Real.exp (-x * Real.cosh r) - (t^2/2) * (r * Real.sinh r * Real.exp (-x * Real.cosh r)) ≤
      Real.exp (-x * Real.cosh r) * Real.cos (t*r) from by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hs := Real.self_le_sinh_iff.mpr hr.le
    have hc := Real.one_sub_sq_div_two_le_cos (x := t*r)
    have hs2 : r^2 ≤ r * Real.sinh r := by
      nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hs)]
    have ht : t^2*r^2 ≤ t^2*(r*Real.sinh r) := mul_le_mul_of_nonneg_left hs2 (sq_nonneg t)
    have hcos : 1-(t^2/2)*(r*Real.sinh r) ≤ Real.cos (t*r) := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hcos (Real.exp_pos (-x*Real.cosh r)).le
    nlinarith)
  rw [integral_sub (kernel_zero_integrable hx) ((sinhMoment_integrable hx).const_mul (t^2/2)),
    integral_const_mul] at h
  simpa only [K, sinhMoment, zero_mul, Real.cos_zero, mul_one] using h

/-- Eventual positivity proved directly, without a Bessel asymptotic. -/
theorem K_pos_of_large (t : ℝ) {x : ℝ} (hx : 0 < x) (hlarge : t^2/2 < x) :
    0 < K t x := by
  have hid := sinhMoment_identity hx
  have hk := K_zero_pos hx
  have hj : 0 < sinhMoment x := by nlinarith
  have hp := mul_pos (sub_pos.mpr hlarge) hj
  have hl := K_lower_integral t hx
  nlinarith

#print axioms sinhMoment_identity
#print axioms K_lower_integral
#print axioms K_pos_of_large

end MaassKBessel

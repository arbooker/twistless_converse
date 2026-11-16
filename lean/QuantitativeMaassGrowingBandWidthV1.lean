module

public import QuantitativeMaassLocalScaleV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Filter
open scoped Topology

namespace QuantitativeMaass

theorem fourthRootScale_le_loglog :
    ∀ᶠ t in atTop,fourthRootScale t≤Real.log (Real.log t) := by
  filter_upwards [slowScale_tendsto.eventually (eventually_ge_atTop (1:ℝ)),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
      (eventually_gt_atTop (0:ℝ))] with t ht hl
  change 0<Real.log (Real.log t) at hl
  have h1 : Real.sqrt (slowScale t)≤slowScale t := by
    have hh := Real.sq_sqrt (by linarith : 0≤slowScale t)
    nlinarith [Real.sqrt_nonneg (slowScale t)]
  have h2 : Real.sqrt (Real.sqrt (slowScale t))≤Real.sqrt (slowScale t) := by
    have hh := Real.sq_sqrt (Real.sqrt_nonneg (slowScale t))
    have hs := Real.sq_sqrt (by linarith : 0≤slowScale t)
    have hge : 1≤Real.sqrt (slowScale t) := by nlinarith [Real.sqrt_nonneg (slowScale t)]
    nlinarith [Real.sqrt_nonneg (Real.sqrt (slowScale t))]
  exact h2.trans (h1.trans ((Real.log_le_sub_one_of_pos hl).trans (by linarith)))

/-- An exponential of the reconstruction scale is still a sublinear
spectral width. -/
theorem exponential_band_width_sublinear (K : ℝ) (hK : 0≤K) :
    Tendsto (fun t => Real.exp (K*fourthRootScale t)/t) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop K (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero
  have hm : Tendsto (fun t : ℝ => (Real.log t)^K/t) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using hh
  apply squeeze_zero' _ _ hm
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    positivity
  · filter_upwards [fourthRootScale_le_loglog,eventually_gt_atTop (0:ℝ),
      Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with t ht ht0 hl
    apply div_le_div_of_nonneg_right _ ht0.le
    rw [Real.rpow_def_of_pos hl]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left ht hK
    nlinarith only [h]

theorem exponential_band_width_quarter (K : ℝ) (hK : 0≤K) :
    ∀ᶠ t in atTop,1≤Real.exp (K*fourthRootScale t) ∧
      Real.exp (K*fourthRootScale t)≤t/4 := by
  filter_upwards [(exponential_band_width_sublinear K hK).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/4)),
    eventually_gt_atTop (0:ℝ)] with t ht ht0
  constructor
  · exact Real.one_le_exp (mul_nonneg hK (Real.sqrt_nonneg _))
  · have hh := (div_lt_iff₀ ht0).mp ht
    linarith

#print axioms fourthRootScale_le_loglog
#print axioms exponential_band_width_sublinear
#print axioms exponential_band_width_quarter

end QuantitativeMaass

module

public import QuantitativeMaassStrongMomentScheduleV1
public import QuantitativeMaassLocalScaleV1
public import QuantitativeMaassGrowingBandWidthV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace QuantitativeMaass.Strong

theorem strongScale_le_loglog :
    ∀ᶠ t in atTop,strongScale t≤Real.log (Real.log t) := by
  have hh := (isLittleO_pow_exp_pos_mul_atTop 2 (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp slowScale_tendsto
  simp only [one_mul] at hh
  filter_upwards [hh.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
      (eventually_gt_atTop (0:ℝ))] with t ht hl
  have hb := (div_le_one (Real.exp_pos (slowScale t))).mp ht.le
  change (slowScale t)^2≤Real.log (Real.log t)
  rw [show Real.exp (slowScale t)=Real.log (Real.log t) from Real.exp_log hl] at hb
  exact hb

theorem exponential_band_width_sublinear (K : ℝ) (hK : 0≤K) :
    Tendsto (fun t => Real.exp (K*strongScale t)/t) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop K (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero
  have hm : Tendsto (fun t : ℝ => (Real.log t)^K/t) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using hh
  apply squeeze_zero' _ _ hm
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    positivity
  · filter_upwards [strongScale_le_loglog,eventually_gt_atTop (0:ℝ),
      Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with t ht ht0 hl
    apply div_le_div_of_nonneg_right _ ht0.le
    rw [Real.rpow_def_of_pos hl]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left ht hK
    nlinarith only [h]

theorem exponential_band_width_quarter (K : ℝ) (hK : 0≤K) :
    ∀ᶠ t in atTop,1≤Real.exp (K*strongScale t) ∧ Real.exp (K*strongScale t)≤t/4 := by
  filter_upwards [(exponential_band_width_sublinear K hK).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/4)),
    eventually_gt_atTop (0:ℝ),slowScale_tendsto.eventually (eventually_ge_atTop (0:ℝ))] with t ht ht0 hs
  constructor
  · exact Real.one_le_exp (mul_nonneg hK (sq_nonneg _))
  · have hh := (div_lt_iff₀ ht0).mp ht
    linarith

theorem strongScale_uniform_centres :
    ∀ᶠ t in atTop,∀ s : ℝ,t/2≤s → strongScale t/4≤strongScale s := by
  have hh : Tendsto (fun t : ℝ => t/2) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num : (0:ℝ)<2) tendsto_id
  filter_upwards [slowScale_half_lower,
    slowScale_tendsto.eventually (eventually_ge_atTop (0:ℝ)),
    hh.eventually (eventually_gt_atTop (0:ℝ)),
    (Real.tendsto_log_atTop.comp hh).eventually (eventually_gt_atTop (0:ℝ)),
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hh)).eventually
      (eventually_gt_atTop (0:ℝ))] with t ht ht0 h0 h1 h2
  intro s hs
  have hb := ht.trans (Real.log_le_log h2 (Real.log_le_log h1 (Real.log_le_log h0 hs)))
  change slowScale t/2≤slowScale s at hb
  have hb0 : 0≤slowScale s := (by positivity : 0≤slowScale t/2).trans hb
  have hp := pow_le_pow_left₀ (by positivity : 0≤slowScale t/2) hb 2
  dsimp only [strongScale]
  nlinarith only [hp]

#print axioms strongScale_le_loglog
#print axioms exponential_band_width_sublinear
#print axioms exponential_band_width_quarter
#print axioms strongScale_uniform_centres
end QuantitativeMaass.Strong

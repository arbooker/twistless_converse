module

public import QuantitativeMaassRawHorizonTraceScaleV1

set_option autoImplicit false
set_option maxHeartbeats 200000
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace QuantitativeMaass.Strong

/-- The square of the triple logarithm pays for growing Newton coefficients. -/
def strongScale (t : ℝ) : ℝ := (slowScale t)^2

theorem strongScale_tendsto : Tendsto strongScale atTop atTop := by
  apply tendsto_atTop_mono' atTop _ slowScale_tendsto
  filter_upwards [slowScale_tendsto.eventually (eventually_ge_atTop (1:ℝ))] with t ht
  dsimp only [strongScale]
  nlinarith

theorem strongScale_div_log :
    Tendsto (fun t : ℝ => strongScale t/Real.log t) atTop (𝓝 0) := by
  have hh := (isLittleO_pow_exp_pos_mul_atTop 2 (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp slowScale_tendsto
  simp only [one_mul] at hh
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have hm := hh.mul hl
  simp only [mul_zero] at hm
  apply hm.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_gt_atTop (0:ℝ))] with t ht
  simp only [Function.comp_apply] at ht ⊢
  rw [show Real.exp (slowScale t)=Real.log (Real.log t) from Real.exp_log ht]
  dsimp only [strongScale,id]
  field_simp

#print axioms strongScale_tendsto
#print axioms strongScale_div_log
end QuantitativeMaass.Strong

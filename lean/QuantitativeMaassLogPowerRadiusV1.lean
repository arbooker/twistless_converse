module

public import QuantitativeMaassLogScaleGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- Positive logarithmic-power propagation radius; the exponential expression
also defines it for all real spectral centres. -/
def logPowerRadius (c t : ℝ) : ℝ := max 1 (Real.exp (c*Real.log (Real.log t)))

theorem logPowerRadius_pos (c t : ℝ) : 0<logPowerRadius c t :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem logPowerRadius_eventually_eq (c : ℝ) (hc : 0<c) :
    ∀ᶠ t in atTop,logPowerRadius c t=Real.exp (c*Real.log (Real.log t)) := by
  filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (0:ℝ))] with t ht
  exact max_eq_right (Real.one_le_exp (mul_nonneg hc.le ht))

theorem logPowerRadius_tendsto (c : ℝ) (hc : 0<c) :
    Tendsto (logPowerRadius c) atTop atTop := by
  have h := Real.tendsto_exp_atTop.comp
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).const_mul_atTop hc)
  apply h.congr'
  filter_upwards [logPowerRadius_eventually_eq c hc] with t ht
  exact ht.symm

/-- Every exponent strictly between zero and one meets the improved geometric budget. -/
theorem logPowerRadius_div_log (c : ℝ) (hc : 0<c) (hc1 : c<1) :
    Tendsto (fun t => logPowerRadius c t/Real.log t) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).const_mul_atTop (sub_pos.mpr hc1))
  apply h.congr'
  filter_upwards [logPowerRadius_eventually_eq c hc,
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with t ht hp
  dsimp only [Function.comp_apply]
  rw [ht,← Real.exp_log hp,← Real.exp_sub]
  simp only [Real.log_exp]
  congr 1
  ring

/-- Logarithmic powers eventually dominate the theorem's triple logarithm. -/
theorem slowScale_le_logPowerRadius_eventually (c : ℝ) (hc : 0<c) :
    ∀ᶠ t in atTop,slowScale t≤logPowerRadius c t := by
  have h : Tendsto (fun x : ℝ => Real.exp (c*x)/x) atTop atTop := by
    simpa only [Real.rpow_one] using tendsto_exp_mul_div_rpow_atTop 1 c hc
  have hl := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [(h.comp hl).eventually (eventually_ge_atTop (1:ℝ)),
    hl.eventually (eventually_gt_atTop (0:ℝ))] with t ht hp
  dsimp only [Function.comp_apply] at ht hp
  have hle : Real.log (Real.log t)≤Real.exp (c*Real.log (Real.log t)) := by
    simpa only [one_mul] using (le_div_iff₀ hp).mp ht
  calc
    slowScale t ≤ Real.log (Real.log t) := by
      exact (Real.log_le_sub_one_of_pos hp).trans (by linarith)
    _ ≤ Real.exp (c*Real.log (Real.log t)) := hle
    _ ≤ logPowerRadius c t := le_max_right _ _

/-- The faster radius resolves every width in the original shrinking-window theorem. -/
theorem logPowerRadius_resolves_width (c : ℝ) (hc : 0<c)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => logPowerRadius c t*ε t) atTop atTop := by
  apply tendsto_atTop_mono' _ _ hproduct
  filter_upwards [hε,slowScale_le_logPowerRadius_eventually c hc] with t he ht
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left ht he.le

#print axioms logPowerRadius_pos
#print axioms logPowerRadius_eventually_eq
#print axioms logPowerRadius_tendsto
#print axioms logPowerRadius_div_log
#print axioms slowScale_le_logPowerRadius_eventually
#print axioms logPowerRadius_resolves_width

end QuantitativeMaass

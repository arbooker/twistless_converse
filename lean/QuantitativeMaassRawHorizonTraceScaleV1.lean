module

public import QuantitativeMaassRawHorizonScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace QuantitativeMaass

theorem slowScale_le_log_eventually :
    ∀ᶠ t : ℝ in atTop,slowScale t≤Real.log t := by
  filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_gt_atTop (0:ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with t hll hl
  simp only [Function.comp_apply] at hll
  have h₁ := Real.log_le_sub_one_of_pos hll
  have h₂ := Real.log_le_sub_one_of_pos hl
  change Real.log (Real.log (Real.log t))≤Real.log t
  linarith

theorem slowScale_div_log_tendsto :
    Tendsto (fun t : ℝ => slowScale t/Real.log t) atTop (𝓝 0) := by
  have hm := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  apply squeeze_zero' _ _ hm
  · filter_upwards [slowScale_tendsto.eventually (eventually_ge_atTop (0:ℝ)),
      Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with t hs ht
    positivity
  · filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
      (eventually_gt_atTop (0:ℝ)),
      Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with t hll hl
    simp only [Function.comp_apply] at hll
    apply div_le_div_of_nonneg_right _ hl.le
    exact (Real.log_le_sub_one_of_pos hll).trans (by linarith)

theorem shrinking_propagation_div_log (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => propagation (slowScale t) (ε t)/Real.log t) atTop (𝓝 0) := by
  have hm := (shrinking_window_parameters ε hε hproduct).1.mul slowScale_div_log_tendsto
  simp only [mul_zero] at hm
  apply hm.congr'
  filter_upwards [slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with t ht
  field_simp

/-- A sublogarithmic logarithm of the geometric cost is absorbed by the
square-root spectral saving, including division by the shrinking width. -/
theorem sqrt_geometric_cost_tendsto (ε F : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hF : Tendsto (fun t => F t/Real.log t) atTop (𝓝 0)) :
    Tendsto (fun t => Real.sqrt t*Real.exp (F t)/(t*ε t)) atTop (𝓝 0) := by
  have hw : Tendsto (fun t => ε t*Real.log t) atTop atTop := by
    apply tendsto_atTop_mono' _ _ hproduct
    filter_upwards [hε,slowScale_le_log_eventually] with t he ht
    exact mul_le_mul_of_nonneg_left ht he.le
  have hm := propagation_excess_tendsto Real.log ε F 1 (1/2)
    (by norm_num) (by norm_num) Real.tendsto_log_atTop hε hw hF
  apply hm.congr'
  filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
  have hs : Real.exp (Real.log t/2)=Real.sqrt t := by
    have hh : (Real.exp (Real.log t/2))^2=t := by
      rw [←Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show (2:ℝ)*(Real.log t/2)=Real.log t by ring,Real.exp_log ht]
    nlinarith [Real.sq_sqrt ht.le,Real.sqrt_nonneg t,Real.exp_pos (Real.log t/2)]
  rw [one_mul,show (1/2:ℝ)*Real.log t=Real.log t/2 by ring,Real.exp_sub,hs]
  have hsq := Real.sq_sqrt ht.le
  have hsp := Real.sqrt_pos.mpr ht
  field_simp
  nlinarith only [hsq]

/-- At the explicit integer horizon, the double-exponential branch cost
and every fixed propagation loss are simultaneously negligible in the
normalized square-root trace error. -/
theorem rawBlockHorizon_geometric_decay (ε : ℝ → ℝ) (C D : ℝ) (hC : 0≤C)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.sqrt t*Real.exp (Real.exp (C*(4:ℝ)^rawBlockHorizon t))*
      Real.exp (D*propagation (slowScale t) (ε t))/(t*ε t)) atTop (𝓝 0) := by
  have hm := (rawBlockHorizon_log_cost C hC).add
    ((shrinking_propagation_div_log ε hε hproduct).const_mul D)
  simp only [mul_zero,add_zero] at hm
  have hh := sqrt_geometric_cost_tendsto ε
    (fun t => Real.exp (C*(4:ℝ)^rawBlockHorizon t)+D*propagation (slowScale t) (ε t))
    hε hproduct (by simpa only [add_div,mul_div_assoc] using hm)
  simpa only [Real.exp_add,mul_assoc] using hh

#print axioms slowScale_le_log_eventually
#print axioms slowScale_div_log_tendsto
#print axioms shrinking_propagation_div_log
#print axioms sqrt_geometric_cost_tendsto
#print axioms rawBlockHorizon_geometric_decay
end QuantitativeMaass

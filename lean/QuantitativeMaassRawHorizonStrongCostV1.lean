module

public import QuantitativeMaassRawHorizonPowerDecayV1
public import QuantitativeMaassStrongScaleV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace QuantitativeMaass

/-- A propagation scale negligible compared with the triple logarithm
is also negligible compared with the logarithm of the spectral center. -/
theorem subslow_div_log (R : ℝ→ℝ)
    (hR : Tendsto (fun t => R t/slowScale t) atTop (𝓝 0)) :
    Tendsto (fun t => R t/Real.log t) atTop (𝓝 0) := by
  have hh := hR.mul slowScale_div_log_tendsto
  rw [mul_zero] at hh
  apply hh.congr'
  filter_upwards [slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with t ht
  field_simp

/-- Raw double-exponential branch cost, fixed powers of the chosen cusp
height, and propagation losses all fit within the square-root trace saving.
The stronger height allowance is used only for geometric errors. -/
theorem rawBlockHorizon_strong_geometric_decay (ε R : ℝ→ℝ) (A B C D E : ℝ) (hC : 0≤C)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hR : Tendsto (fun t => R t/slowScale t) atTop (𝓝 0)) :
    Tendsto (fun t => Real.sqrt t*
      Real.exp (A*Real.exp (C*(4:ℝ)^rawBlockHorizon t)+B*R t+D*Strong.strongScale t+E)/
        (t*ε t)) atTop (𝓝 0) := by
  have hraw := (rawBlockHorizon_log_cost C hC).const_mul A
  have hprop := (subslow_div_log R hR).const_mul B
  have hheight := Strong.strongScale_div_log.const_mul D
  have hc := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul E
  have hh := ((hraw.add hprop).add hheight).add hc
  simp only [mul_zero,add_zero] at hh
  apply sqrt_geometric_cost_tendsto ε _ hε hp
  convert hh using 1
  funext t
  simp only [Function.comp_apply]
  ring

#print axioms subslow_div_log
#print axioms rawBlockHorizon_strong_geometric_decay
end QuantitativeMaass

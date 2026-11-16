module

public import QuantitativeMaassRawHorizonTraceScaleV1
public import QuantitativeMaassLVGeometricLowerV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace QuantitativeMaass

/-- Squaring the raw horizon gives an LV degree whose square-root deficit
has precisely the already controlled inverse-horizon saving. -/
def growingLVDegree (t : ℝ) : ℕ := (4^rawBlockHorizon t)^2

theorem growingLVDegree_pos (t : ℝ) : 0<growingLVDegree t := by
  unfold growingLVDegree
  positivity

theorem sqrt_growingLVDegree (t : ℝ) :
    Real.sqrt (growingLVDegree t:ℝ)=(4:ℝ)^rawBlockHorizon t := by
  simp only [growingLVDegree,Nat.cast_pow,Nat.cast_ofNat]
  exact Real.sqrt_sq (by positivity)

/-- Every fixed propagation loss is absorbed by the actual spherical
LV deficit at the original window-width hypothesis. -/
theorem growingLV_deficit_decay (p : ℕ) (ε : ℝ→ℝ) (C : ℝ) (hC : 0≤C)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (C*propagation (slowScale t) (ε t))*
      lvSphericalDeficit p (growingLVDegree t)/ε t) atTop (𝓝 0) := by
  have hh := (rawBlockHorizon_propagation_decay ε C hC hε hproduct).const_mul
    (unramifiedDensityBound (p:ℝ)*lvBound p*Real.sqrt Real.pi)
  simp only [mul_zero] at hh
  convert hh using 1
  funext t
  rw [lvSphericalDeficit,sqrt_growingLVDegree]
  ring

/-- The polynomial degree is sublogarithmic, allowing an exponential
coefficient and time-support cost without losing the square-root saving. -/
theorem growingLVDegree_div_log_tendsto :
    Tendsto (fun t : ℝ => (growingLVDegree t:ℝ)/Real.log t) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (rawBlockHorizon_log_cost 2 (by norm_num))
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with t ht
    positivity
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with t ht
    apply div_le_div_of_nonneg_right _ ht.le
    simp only [growingLVDegree,Nat.cast_pow,Nat.cast_ofNat]
    have h : (4:ℝ)^rawBlockHorizon t≤Real.exp ((4:ℝ)^rawBlockHorizon t) :=
      by linarith [Real.add_one_le_exp ((4:ℝ)^rawBlockHorizon t)]
    have hp := pow_le_pow_left₀ (by positivity : 0≤(4:ℝ)^rawBlockHorizon t) h 2
    rw [←Real.exp_nat_mul] at hp
    simpa only [Nat.cast_ofNat] using hp

/-- Simultaneous degree and propagation costs vanish after normalization,
without a stronger condition on the shrinking window. -/
theorem growingLV_geometric_decay (ε : ℝ→ℝ) (B D : ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.sqrt t*
      Real.exp (B*(growingLVDegree t:ℝ)+D*propagation (slowScale t) (ε t))/(t*ε t))
      atTop (𝓝 0) := by
  apply sqrt_geometric_cost_tendsto ε _ hε hproduct
  have hh := (growingLVDegree_div_log_tendsto.const_mul B).add
    ((shrinking_propagation_div_log ε hε hproduct).const_mul D)
  simpa only [mul_zero,add_zero,add_div,mul_div_assoc] using hh

#print axioms growingLVDegree_pos
#print axioms sqrt_growingLVDegree
#print axioms growingLV_deficit_decay
#print axioms growingLVDegree_div_log_tendsto
#print axioms growingLV_geometric_decay
end QuantitativeMaass

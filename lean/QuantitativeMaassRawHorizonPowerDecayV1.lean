module

public import QuantitativeMaassRawHorizonTraceScaleV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace QuantitativeMaass

/-- Every fixed geometric recovery rate at the actual raw integer horizon
has a positive exponential saving in the triple logarithm. -/
theorem rawBlockHorizon_power_bound (q : ℝ) (hq : 0<q) (hq1 : q<1) (t : ℝ) :
    q^rawBlockHorizon t≤q⁻¹*Real.exp (-((-Real.log q)/(2*Real.log 4))*slowScale t) := by
  have h4 : 0<Real.log 4 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (Real.exp_pos (slowScale t/2)) (rawBlockHorizon_lower t)
  rw [Real.log_exp,Real.log_mul (by norm_num : (4:ℝ)≠0) (by positivity),Real.log_pow] at hlog
  have hn : slowScale t/(2*Real.log 4)≤(rawBlockHorizon t:ℝ)+1 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) h4)).mpr
    nlinarith only [hlog]
  have hh := mul_le_mul_of_nonpos_right hn (Real.log_neg hq hq1).le
  have he : (rawBlockHorizon t:ℝ)*Real.log q≤
      -((-Real.log q)/(2*Real.log 4))*slowScale t-Real.log q := by
    calc
      _ ≤ (slowScale t/(2*Real.log 4))*Real.log q-Real.log q := by linarith
      _ = _ := by ring
  calc
    _ = Real.exp ((rawBlockHorizon t:ℝ)*Real.log q) := by rw [Real.exp_nat_mul,Real.exp_log hq]
    _ ≤ Real.exp (-((-Real.log q)/(2*Real.log 4))*slowScale t-Real.log q) := Real.exp_le_exp.mpr he
    _ = _ := by rw [Real.exp_sub,Real.exp_log hq]; ring

/-- The raw physical recovery and regular excess rates tolerate any fixed
propagation loss, including division by the original window width. -/
theorem rawBlockHorizon_power_decay (ε R : ℝ→ℝ) (q C : ℝ)
    (hq : 0<q) (hq1 : q<1) (hC : 0≤C)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hR : Tendsto (fun t => R t/slowScale t) atTop (𝓝 0)) :
    Tendsto (fun t => Real.exp (C*R t)*q^rawBlockHorizon t/ε t) atTop (𝓝 0) := by
  let c := (-Real.log q)/(2*Real.log 4)
  have hc : 0<c := div_pos (neg_pos.mpr (Real.log_neg hq hq1))
    (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
  have hh := (propagation_excess_tendsto slowScale ε R C c hC hc slowScale_tendsto hε hp hR).const_mul q⁻¹
  rw [mul_zero] at hh
  apply squeeze_zero' _ _ hh
  · filter_upwards [hε] with t ht
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hq.le _)) ht.le
  · filter_upwards [hε] with t ht
    calc
      _ ≤ Real.exp (C*R t)*(q⁻¹*Real.exp (-c*slowScale t))/ε t :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (rawBlockHorizon_power_bound q hq hq1 t) (Real.exp_pos _).le) ht.le
      _ = q⁻¹*(Real.exp (C*R t-c*slowScale t)/ε t) := by rw [sub_eq_add_neg,Real.exp_add]; ring

#print axioms rawBlockHorizon_power_bound
#print axioms rawBlockHorizon_power_decay
end QuantitativeMaass

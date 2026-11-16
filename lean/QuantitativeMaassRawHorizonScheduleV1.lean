module

public import QuantitativeMaassParametersV1
public import Mathlib.Data.Nat.Log

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Filter
open scoped Topology
namespace QuantitativeMaass

/-- Integer block horizon for the raw residual filter. Its fourth power
scale is comparable to the square root of the double logarithm. -/
def rawBlockHorizon (t : ℝ) : ℕ :=
  Nat.log 4 ⌈Real.exp (slowScale t/2)⌉₊

theorem rawBlockHorizon_lower (t : ℝ) :
    Real.exp (slowScale t/2)≤4*(4:ℝ)^rawBlockHorizon t := by
  have hn : (⌈Real.exp (slowScale t/2)⌉₊:ℝ)<(4:ℝ)^(rawBlockHorizon t+1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1<(4:ℕ))
      ⌈Real.exp (slowScale t/2)⌉₊
  have hh := (Nat.le_ceil (Real.exp (slowScale t/2))).trans hn.le
  simpa only [pow_succ,mul_comm] using hh

theorem rawBlockHorizon_upper :
    ∀ᶠ t in atTop,(4:ℝ)^rawBlockHorizon t≤2*Real.exp (slowScale t/2) := by
  filter_upwards [slowScale_tendsto.eventually (eventually_ge_atTop (0:ℝ))] with t ht
  have he : 1≤Real.exp (slowScale t/2) := Real.one_le_exp (by positivity)
  have hn : ⌈Real.exp (slowScale t/2)⌉₊≠0 := by
    intro hz
    have hh := Nat.le_ceil (Real.exp (slowScale t/2))
    rw [hz,Nat.cast_zero] at hh
    linarith
  have hp : (4:ℝ)^rawBlockHorizon t≤(⌈Real.exp (slowScale t/2)⌉₊:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 4 hn
  have hc := (Nat.ceil_lt_add_one (Real.exp_pos (slowScale t/2)).le).le
  linarith

/-- The actual inverse horizon saving absorbs every fixed propagation
loss at the original triple-logarithmic width threshold. -/
theorem rawBlockHorizon_propagation_decay (ε : ℝ → ℝ) (C : ℝ) (hC : 0≤C)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (C*propagation (slowScale t) (ε t))/
      ((4:ℝ)^rawBlockHorizon t*ε t)) atTop (𝓝 0) := by
  have hlim := (chosen_propagation_excess slowScale ε C (1/2) hC
    (by norm_num) slowScale_tendsto hε hproduct).const_mul 4
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hε] with t he
    positivity
  · filter_upwards [hε] with t he
    have hp : 0<(4:ℝ)^rawBlockHorizon t := by positivity
    have hl := rawBlockHorizon_lower t
    have hi : 1/(4:ℝ)^rawBlockHorizon t≤4/Real.exp (slowScale t/2) := by
      apply (div_le_div_iff₀ hp (Real.exp_pos _)).mpr
      simpa only [one_mul] using hl
    have hm := mul_le_mul_of_nonneg_left hi
      (show 0≤Real.exp (C*propagation (slowScale t) (ε t))/ε t by positivity)
    convert hm using 1
    · ring
    · rw [Real.exp_sub]
      ring

/-- Even the logarithm of the double-exponential expression envelope
is negligible relative to log t at the same integer horizon. -/
theorem rawBlockHorizon_log_cost (C : ℝ) (hC : 0≤C) :
    Tendsto (fun t => Real.exp (C*(4:ℝ)^rawBlockHorizon t)/Real.log t)
      atTop (𝓝 0) := by
  have hr : Tendsto (fun t => Real.exp (slowScale t/2)) atTop atTop := by
    exact Real.tendsto_exp_atTop.comp
      (by simpa only [mul_comm,div_eq_mul_inv,one_mul] using
        slowScale_tendsto.const_mul_atTop (by norm_num : (0:ℝ)<1/2))
  have hm := Real.tendsto_exp_neg_atTop_nhds_zero.comp hr
  apply squeeze_zero' _ _ hm
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with t ht
    positivity
  · filter_upwards [rawBlockHorizon_upper,hr.eventually (eventually_ge_atTop (2*C+1)),
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
        (eventually_gt_atTop (0:ℝ)),
      Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with t hn hb hll hl
    have hs : (Real.exp (slowScale t/2))^2=Real.log (Real.log t) := by
      rw [←Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show (2:ℝ)*(slowScale t/2)=slowScale t by ring]
      exact Real.exp_log hll
    have hbound : C*(4:ℝ)^rawBlockHorizon t-Real.log (Real.log t)≤
        -Real.exp (slowScale t/2) := by
      have hh := mul_le_mul_of_nonneg_left hn hC
      have hb' := mul_le_mul_of_nonneg_right hb (Real.exp_pos (slowScale t/2)).le
      nlinarith only [hh,hb',hs]
    rw [←Real.exp_log hl,←Real.exp_sub]
    exact Real.exp_le_exp.mpr hbound

#print axioms rawBlockHorizon_lower
#print axioms rawBlockHorizon_upper
#print axioms rawBlockHorizon_propagation_decay
#print axioms rawBlockHorizon_log_cost
end QuantitativeMaass

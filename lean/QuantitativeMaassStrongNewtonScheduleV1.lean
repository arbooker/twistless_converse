module

public import QuantitativeMaassStrongMomentScheduleV1
public import Mathlib.Data.Nat.Log

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Filter
open scoped Topology

namespace QuantitativeMaass.Strong

/-- Newton depth grows slowly enough that its coefficient cost is absorbed
by the proved weighted exceptional estimate. -/
def bandNewtonDepth (t : ℝ) : ℕ := Nat.log 4 ⌈strongScale t⌉₊

theorem bandNewtonDepth_cost_bound :
    ∀ᶠ t in atTop,((4:ℝ)^(bandNewtonDepth t))≤2*strongScale t := by
  filter_upwards [strongScale_tendsto.eventually (eventually_ge_atTop (1:ℝ))] with t ht
  have hn : ⌈strongScale t⌉₊≠0 := by
    intro hz
    have hh := Nat.le_ceil (strongScale t)
    rw [hz,Nat.cast_zero] at hh
    linarith
  have hp : (4:ℝ)^(bandNewtonDepth t)≤(⌈strongScale t⌉₊:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 4 hn
  have hc := (Nat.ceil_lt_add_one (by unfold strongScale; positivity : 0≤strongScale t)).le
  linarith

theorem bandNewtonDepth_exponent_lower (t : ℝ) :
    Real.sqrt (strongScale t)≤2*(2:ℝ)^(bandNewtonDepth t) := by
  have hn : (⌈strongScale t⌉₊:ℝ)<(4:ℝ)^(bandNewtonDepth t+1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1<(4:ℕ)) ⌈strongScale t⌉₊
  have ht := (Nat.le_ceil (strongScale t)).trans_lt hn
  have he : (4:ℝ)^(bandNewtonDepth t+1)=(2*(2:ℝ)^(bandNewtonDepth t))^2 := by
    rw [pow_succ,show (4:ℝ)=2^2 by norm_num,←pow_mul, Nat.mul_comm 2, pow_mul]
    ring
  rw [he] at ht
  have hs := Real.sq_sqrt (show 0≤strongScale t by unfold strongScale; positivity)
  nlinarith [Real.sqrt_nonneg (strongScale t),pow_pos (by norm_num : (0:ℝ)<2) (bandNewtonDepth t)]

/-- Newton error absorbs every fixed propagation loss. Its exponent is
linear in the triple logarithm, while propagation is smaller than that scale. -/
theorem bandNewtonDepth_weighted_decay (ε : ℝ→ℝ) (q C : ℝ)
    (hq : 0<q) (hq1 : q<1) (hC : 0≤C)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (C*propagation (slowScale t) (ε t))*
      q^(2^(bandNewtonDepth t))/ε t) atTop (𝓝 0) := by
  have hl : Real.log q<0 := Real.log_neg hq hq1
  have hh := chosen_propagation_excess slowScale ε C (-Real.log q/2) hC
    (by linarith) slowScale_tendsto hε hproduct
  apply squeeze_zero' _ _ hh
  · filter_upwards [hε] with t he
    positivity
  · filter_upwards [hε,slowScale_tendsto.eventually (eventually_ge_atTop (0:ℝ))] with t he ht
    apply div_le_div_of_nonneg_right _ he.le
    have hn := bandNewtonDepth_exponent_lower t
    rw [strongScale,Real.sqrt_sq ht] at hn
    have hqpow : q^(2^(bandNewtonDepth t))=
        Real.exp (((2^(bandNewtonDepth t):ℕ):ℝ)*Real.log q) := by
      rw [Real.exp_nat_mul,Real.exp_log hq]
    rw [hqpow,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonpos_left hn hl.le
    push_cast
    nlinarith only [hm]

#print axioms strongScale_tendsto
#print axioms bandNewtonDepth_cost_bound
#print axioms bandNewtonDepth_exponent_lower
#print axioms bandNewtonDepth_weighted_decay
end QuantitativeMaass.Strong

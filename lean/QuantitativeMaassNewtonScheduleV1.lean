module

public import QuantitativeMaassWeightedWidthDecayV1
public import Mathlib.Data.Nat.Log

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Filter
open scoped Topology

namespace QuantitativeMaass

/-- Newton depth grows slowly enough that its coefficient cost is absorbed
by the proved weighted exceptional estimate. -/
def bandNewtonDepth (t : ℝ) : ℕ := Nat.log 4 ⌈fourthRootScale t⌉₊

theorem bandNewtonDepth_cost_bound :
    ∀ᶠ t in atTop,((4:ℝ)^(bandNewtonDepth t))≤2*fourthRootScale t := by
  filter_upwards [fourthRootScale_tendsto.eventually (eventually_ge_atTop (1:ℝ))] with t ht
  have hn : ⌈fourthRootScale t⌉₊≠0 := by
    intro hz
    have hh := Nat.le_ceil (fourthRootScale t)
    rw [hz,Nat.cast_zero] at hh
    linarith
  have hp : (4:ℝ)^(bandNewtonDepth t)≤(⌈fourthRootScale t⌉₊:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 4 hn
  have hc := (Nat.ceil_lt_add_one (by unfold fourthRootScale; positivity : 0≤fourthRootScale t)).le
  linarith

theorem bandNewtonDepth_exponent_lower (t : ℝ) :
    Real.sqrt (fourthRootScale t)≤2*(2:ℝ)^(bandNewtonDepth t) := by
  have hn : (⌈fourthRootScale t⌉₊:ℝ)<(4:ℝ)^(bandNewtonDepth t+1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1<(4:ℕ)) ⌈fourthRootScale t⌉₊
  have ht := (Nat.le_ceil (fourthRootScale t)).trans_lt hn
  have he : (4:ℝ)^(bandNewtonDepth t+1)=(2*(2:ℝ)^(bandNewtonDepth t))^2 := by
    rw [pow_succ,show (4:ℝ)=2^2 by norm_num,←pow_mul, Nat.mul_comm 2, pow_mul]
    ring
  rw [he] at ht
  have hs := Real.sq_sqrt (show 0≤fourthRootScale t by unfold fourthRootScale; positivity)
  nlinarith [Real.sqrt_nonneg (fourthRootScale t),pow_pos (by norm_num : (0:ℝ)<2) (bandNewtonDepth t)]

/-- The actual Newton error exponent still dominates every allowed
inverse window width, although the polynomial cost is much smaller than
the old-space filter's moment scale. -/
theorem bandNewtonDepth_decay (ε : ℝ → ℝ) (q : ℝ) (hq : 0<q) (hq1 : q<1)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => q^(2^(bandNewtonDepth t))/ε t) atTop (𝓝 0) := by
  have hl : Real.log q<0 := Real.log_neg hq hq1
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 8 (-Real.log q/2)
    (by linarith only [hl])).comp (Real.tendsto_sqrt_atTop.comp fourthRootScale_tendsto)
  have hm : Tendsto (fun t => (Real.sqrt (fourthRootScale t))^8*
      Real.exp ((Real.log q/2)*Real.sqrt (fourthRootScale t))) atTop (𝓝 0) := by
    convert hh using 1
    funext t
    simp only [Function.comp_def,Real.rpow_ofNat]
    congr 1
    congr 1
    ring
  apply squeeze_zero' _ _ hm
  · filter_upwards [hε] with t he
    positivity
  · filter_upwards [hε,hproduct.eventually (eventually_ge_atTop (1:ℝ)),
      slowScale_tendsto.eventually (eventually_ge_atTop (0:ℝ))] with t he hp ht
    have hpow : q^(2^(bandNewtonDepth t))≤
        Real.exp ((Real.log q/2)*Real.sqrt (fourthRootScale t)) := by
      have heq : q^(2^(bandNewtonDepth t))=
          Real.exp (((2^(bandNewtonDepth t):ℕ):ℝ)*Real.log q) := by
        rw [Real.exp_nat_mul,Real.exp_log hq]
      rw [heq]
      apply Real.exp_le_exp.mpr
      have hg := mul_le_mul_of_nonpos_left (bandNewtonDepth_exponent_lower t) hl.le
      push_cast
      nlinarith only [hg]
    have hwidth : 1/ε t≤slowScale t := (div_le_iff₀ he).mpr (by nlinarith only [hp])
    have hs : (Real.sqrt (fourthRootScale t))^8=slowScale t := by
      calc
        _ = ((Real.sqrt (fourthRootScale t))^2)^4 := by ring
        _ = _ := by rw [Real.sq_sqrt (show 0≤fourthRootScale t by unfold fourthRootScale; positivity),
          fourthRootScale_pow_four ht]
    rw [hs]
    calc
      _ ≤ Real.exp ((Real.log q/2)*Real.sqrt (fourthRootScale t))/ε t :=
        div_le_div_of_nonneg_right hpow he.le
      _ ≤ _ := by
        have hg := mul_le_mul_of_nonneg_left hwidth
          (Real.exp_pos ((Real.log q/2)*Real.sqrt (fourthRootScale t))).le
        simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using hg

#print axioms bandNewtonDepth_cost_bound
#print axioms bandNewtonDepth_exponent_lower
#print axioms bandNewtonDepth_decay

end QuantitativeMaass

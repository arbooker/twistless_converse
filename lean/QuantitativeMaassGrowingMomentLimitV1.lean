module

public import QuantitativeMaassGeometricLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Filter
open scoped Topology

namespace QuantitativeMaass

/-- The square-root saving absorbs a sub-slow-scale exponential cost even
without a window-width factor in the numerator. -/
theorem growing_moment_geometric_limit (ε F : ℝ → ℝ) (C : ℝ) (hC : 0≤C)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hF : Tendsto (fun t => F t/slowScale t) atTop (𝓝 0)) :
    Tendsto (fun t => C*Real.sqrt t*Real.exp (F t)/(t*ε t)) atTop (𝓝 0) := by
  have hm := (propagation_excess_tendsto slowScale ε F 1 (1/2) zero_le_one (by norm_num)
    slowScale_tendsto hε hproduct hF).const_mul C
  simp only [one_mul,mul_zero] at hm
  apply squeeze_zero' _ _ hm
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    positivity
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ),exp_half_slowScale_le_sqrt_eventually] with t he ht hs
    have hst : 0<Real.sqrt t := Real.sqrt_pos.mpr ht
    have hcancel : C*Real.sqrt t*Real.exp (F t)/(t*ε t)=C*Real.exp (F t)/(Real.sqrt t*ε t) := by
      have hb : Real.sqrt t/t=1/Real.sqrt t := by
        apply (div_eq_div_iff ht.ne' hst.ne').mpr
        nlinarith only [Real.sq_sqrt ht.le]
      calc
        _ = (C*Real.exp (F t)/ε t)*(Real.sqrt t/t) := by ring
        _ = _ := by rw [hb];ring
    rw [hcancel]
    calc
      _ ≤ C*Real.exp (F t)/(Real.exp (slowScale t/2)*ε t) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_right hs he.le)
      _ = _ := by rw [Real.exp_sub];ring

/-- A concrete increasing moment degree, negligible relative to the slow scale. -/
def growingMomentDegree (t : ℝ) : ℕ := ⌈Real.sqrt (slowScale t)⌉₊

theorem growingMomentDegree_div_scale :
    Tendsto (fun t => (growingMomentDegree t:ℝ)/slowScale t) atTop (𝓝 0) := by
  have hs : Tendsto (fun t => Real.sqrt (slowScale t)/slowScale t) atTop (𝓝 0) := by
    have hh := (propagation_limits slowScale (fun _ : ℝ => 1)
      (slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ)))
      (Eventually.of_forall (fun _ => zero_lt_one))
      (by simpa only [one_mul] using slowScale_tendsto)).1
    simpa only [propagation,div_one] using hh
  have hi : Tendsto (fun t => 1/slowScale t) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp slowScale_tendsto
  have hm := hs.add hi
  simp only [add_zero] at hm
  apply squeeze_zero' _ _ hm
  · filter_upwards [slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with t ht
    positivity
  · filter_upwards [slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with t ht
    rw [←add_div]
    exact div_le_div_of_nonneg_right (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le ht.le

/-- Any fixed geometric decay in this degree dominates division by every
allowed shrinking width. This uses only the original width/product condition. -/
theorem growingMomentDegree_decay (ε : ℝ → ℝ) (q : ℝ) (hq : 0<q) (hq1 : q<1)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => q^(growingMomentDegree t)/ε t) atTop (𝓝 0) := by
  have hl : Real.log q<0 := Real.log_neg hq hq1
  have hm : Tendsto (fun t => (Real.sqrt (slowScale t))^2*
      Real.exp (Real.log q*Real.sqrt (slowScale t))) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (-Real.log q) (by linarith only [hl])).comp
      (Real.tendsto_sqrt_atTop.comp slowScale_tendsto)
    simpa only [Real.rpow_two,neg_neg,Function.comp_def] using hh
  apply squeeze_zero' _ _ hm
  · filter_upwards [hε] with t he
    positivity
  · filter_upwards [hε,slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ)),
      hproduct.eventually (eventually_ge_atTop (1:ℝ))] with t he ht hp
    have hn : Real.sqrt (slowScale t)≤(growingMomentDegree t:ℝ) := Nat.le_ceil _
    have hpow : q^(growingMomentDegree t)≤Real.exp (Real.log q*Real.sqrt (slowScale t)) := by
      have heq : q^(growingMomentDegree t)=Real.exp ((growingMomentDegree t:ℝ)*Real.log q) := by
        rw [Real.exp_nat_mul,Real.exp_log hq]
      rw [heq]
      apply Real.exp_le_exp.mpr
      simpa only [mul_comm] using mul_le_mul_of_nonpos_left hn hl.le
    have hi : 1/ε t≤slowScale t := (div_le_iff₀ he).mpr (by nlinarith only [hp])
    calc
      _ ≤ Real.exp (Real.log q*Real.sqrt (slowScale t))/ε t :=
        div_le_div_of_nonneg_right hpow he.le
      _ ≤ slowScale t*Real.exp (Real.log q*Real.sqrt (slowScale t)) := by
        have hh := mul_le_mul_of_nonneg_left hi (Real.exp_pos (Real.log q*Real.sqrt (slowScale t))).le
        simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using hh
      _ = _ := by rw [Real.sq_sqrt ht.le]

/-- Every fixed exponential degree cost is absorbed by the spectral saving. -/
theorem growingMomentDegree_cost (ε : ℝ → ℝ) (b C : ℝ) (hb : 0<b) (hC : 0≤C)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => C*Real.sqrt t*b^(growingMomentDegree t)/(t*ε t)) atTop (𝓝 0) := by
  have hf : Tendsto (fun t => (Real.log b*(growingMomentDegree t:ℝ))/slowScale t) atTop (𝓝 0) := by
    simpa only [mul_div_assoc,mul_zero] using growingMomentDegree_div_scale.const_mul (Real.log b)
  have hh := growing_moment_geometric_limit ε (fun t => Real.log b*(growingMomentDegree t:ℝ)) C hC hε hproduct hf
  convert hh using 1
  funext t
  rw [mul_comm (Real.log b),Real.exp_nat_mul,Real.exp_log hb]

#print axioms growingMomentDegree_cost

#print axioms growing_moment_geometric_limit
#print axioms growingMomentDegree_div_scale
#print axioms growingMomentDegree_decay

end QuantitativeMaass

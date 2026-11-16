module

public import QuantitativeMaassGrowingMomentLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Filter
open scoped Topology

namespace QuantitativeMaass

/-- The fourth-root scale grows more slowly than the moment degree and
allows finite reconstruction polynomials to grow while retaining decay. -/
def fourthRootScale (t : ℝ) : ℝ := Real.sqrt (Real.sqrt (slowScale t))

theorem sqrt_ratio_tendsto_zero (f : ℝ → ℝ) (hf : Tendsto f atTop atTop) :
    Tendsto (fun t => Real.sqrt (f t)/f t) atTop (𝓝 0) := by
  have hh := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hf)
  apply hh.congr'
  filter_upwards [hf.eventually (eventually_gt_atTop (0:ℝ))] with t ht
  have hs : 0<Real.sqrt (f t) := Real.sqrt_pos.mpr ht
  calc
    (Real.sqrt (f t))⁻¹=Real.sqrt (f t)/(Real.sqrt (f t))^2 := by field_simp
    _ = Real.sqrt (f t)/f t := by rw [Real.sq_sqrt ht.le]

theorem fourthRootScale_div_sqrt :
    Tendsto (fun t => fourthRootScale t/Real.sqrt (slowScale t)) atTop (𝓝 0) :=
  sqrt_ratio_tendsto_zero _ (Real.tendsto_sqrt_atTop.comp slowScale_tendsto)

theorem fourthRootScale_div_scale :
    Tendsto (fun t => fourthRootScale t/slowScale t) atTop (𝓝 0) := by
  have hh := fourthRootScale_div_sqrt.mul (sqrt_ratio_tendsto_zero slowScale slowScale_tendsto)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with t ht
  have hs : Real.sqrt (slowScale t)≠0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  field_simp

/-- The exceptional-spectrum decay survives every fixed exponential cost
on the fourth-root reconstruction scale. -/
theorem weighted_growingMomentDegree_decay (ε : ℝ → ℝ) (q C : ℝ)
    (hq : 0<q) (hq1 : q<1)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (C*fourthRootScale t)*q^(growingMomentDegree t)/ε t)
      atTop (𝓝 0) := by
  have hb : 0<Real.sqrt q := Real.sqrt_pos.mpr hq
  have hb1 : Real.sqrt q<1 := by nlinarith [Real.sq_sqrt hq.le,Real.sqrt_nonneg q]
  have hh := growingMomentDegree_decay ε (Real.sqrt q) hb hb1 hε hproduct
  have hl : Real.log q<0 := Real.log_neg hq hq1
  have hw := fourthRootScale_div_sqrt.const_mul C
  simp only [mul_zero] at hw
  apply squeeze_zero' _ _ hh
  · filter_upwards [hε] with t he
    positivity
  · filter_upwards [hε,slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ)),
      hw.eventually (eventually_lt_nhds (by linarith : 0< -Real.log q/2))] with t he ht hw
    apply div_le_div_of_nonneg_right _ he.le
    have hs : 0<Real.sqrt (slowScale t) := Real.sqrt_pos.mpr ht
    have hwd : C*fourthRootScale t≤(-Real.log q/2)*(growingMomentDegree t:ℝ) := by
      have hws : C*fourthRootScale t≤(-Real.log q/2)*Real.sqrt (slowScale t) := by
        apply (div_le_iff₀ hs).mp
        simpa only [mul_div_assoc] using hw.le
      exact hws.trans (mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by linarith only [hl]))
    have hqp : q^(growingMomentDegree t)=Real.exp ((growingMomentDegree t:ℝ)*Real.log q) := by
      rw [Real.exp_nat_mul,Real.exp_log hq]
    have hbp : (Real.sqrt q)^(growingMomentDegree t)=
        Real.exp ((growingMomentDegree t:ℝ)*Real.log (Real.sqrt q)) := by
      rw [Real.exp_nat_mul,Real.exp_log hb]
    rw [hqp,hbp,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [Real.log_sqrt hq.le]
    linarith only [hwd]

/-- The geometric saving also absorbs the growing reconstruction cost. -/
theorem weighted_growingMomentDegree_cost (ε : ℝ → ℝ) (b C W : ℝ)
    (hb : 0<b) (hC : 0≤C)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*fourthRootScale t)*C*Real.sqrt t*b^(growingMomentDegree t)/(t*ε t))
      atTop (𝓝 0) := by
  have hd := growingMomentDegree_div_scale.const_mul (Real.log b)
  have hw := fourthRootScale_div_scale.const_mul W
  have hf : Tendsto (fun t =>
      ((Real.log b)*(growingMomentDegree t:ℝ)+W*fourthRootScale t)/slowScale t) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero,add_div,mul_div_assoc] using hd.add hw
  have hh := growing_moment_geometric_limit ε
    (fun t => (Real.log b)*(growingMomentDegree t:ℝ)+W*fourthRootScale t) C hC hε hproduct hf
  convert hh using 1
  funext t
  rw [Real.exp_add,mul_comm (Real.log b),Real.exp_nat_mul,Real.exp_log hb]
  ring

#print axioms weighted_growingMomentDegree_cost

#print axioms sqrt_ratio_tendsto_zero
#print axioms fourthRootScale_div_sqrt
#print axioms fourthRootScale_div_scale
#print axioms weighted_growingMomentDegree_decay

end QuantitativeMaass

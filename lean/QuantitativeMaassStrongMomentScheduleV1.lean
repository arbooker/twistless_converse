module

public import QuantitativeMaassStrongScaleV1
public import QuantitativeMaassLVGrowingScheduleV1
public import QuantitativeMaassWeightedMomentDecayV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace QuantitativeMaass.Strong

theorem growingLVDegree_exp_lower (t : ℝ) :
    Real.exp (slowScale t)≤16*(growingLVDegree t:ℝ) := by
  have hh := pow_le_pow_left₀ (Real.exp_pos (slowScale t/2)).le (rawBlockHorizon_lower t) 2
  rw [←Real.exp_nat_mul] at hh
  norm_num only [Nat.cast_ofNat] at hh
  rw [show (2:ℝ)*(slowScale t/2)=slowScale t by ring] at hh
  simpa only [growingLVDegree,Nat.cast_pow,Nat.cast_ofNat,mul_pow,show (4:ℝ)^2=16 by norm_num] using hh

theorem strongScale_div_degree :
    Tendsto (fun t : ℝ => strongScale t/(growingLVDegree t:ℝ)) atTop (𝓝 0) := by
  have hh := ((isLittleO_pow_exp_pos_mul_atTop 2 (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp
    slowScale_tendsto).const_mul 16
  simp only [Function.comp_apply,one_mul,mul_zero] at hh
  change Tendsto (fun t => strongScale t/(growingLVDegree t:ℝ)) atTop (𝓝 0)
  change Tendsto (fun t => 16*(strongScale t/Real.exp (slowScale t))) atTop (𝓝 0) at hh
  apply squeeze_zero' _ _ hh
  · filter_upwards [slowScale_tendsto.eventually (eventually_ge_atTop (0:ℝ))] with t ht
    exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [slowScale_tendsto.eventually (eventually_ge_atTop (0:ℝ))] with t ht
    have hd : 0<(growingLVDegree t:ℝ) := by exact_mod_cast growingLVDegree_pos t
    have he := mul_le_mul_of_nonneg_left (growingLVDegree_exp_lower t) (sq_nonneg (slowScale t))
    rw [show 16*(strongScale t/Real.exp (slowScale t))=(16*strongScale t)/Real.exp (slowScale t) by ring]
    apply (div_le_div_iff₀ hd (Real.exp_pos (slowScale t))).mpr
    dsimp only [strongScale]
    nlinarith only [he]

theorem slow_exponential_div_width (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (-slowScale t)/ε t) atTop (𝓝 0) := by
  simpa only [zero_mul,zero_sub,one_mul] using
    chosen_propagation_excess slowScale ε 0 1 (by norm_num) (by norm_num) slowScale_tendsto hε hproduct


theorem strong_exponential_div_width (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (-strongScale t)/ε t) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (slow_exponential_div_width ε hε hproduct)
  · filter_upwards [hε] with t ht
    positivity
  · filter_upwards [hε,slowScale_tendsto.eventually (eventually_ge_atTop (1:ℝ))] with t he ht
    apply div_le_div_of_nonneg_right _ he.le
    apply Real.exp_le_exp.mpr
    dsimp only [strongScale]
    nlinarith

/-- A squared integer horizon beats every fixed exponential loss in the
squared triple-logarithmic scale, rather than just its fourth root. -/
theorem weighted_growingMomentDegree_decay (ε : ℝ→ℝ) (q C : ℝ)
    (hq : 0<q) (hq1 : q<1)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (C*strongScale t)*q^(growingLVDegree t)/ε t) atTop (𝓝 0) := by
  have hlog : Real.log q<0 := Real.log_neg hq hq1
  have hh := strongScale_div_degree.const_mul (C+1)
  simp only [mul_zero] at hh
  apply squeeze_zero' _ _ (strong_exponential_div_width ε hε hproduct)
  · filter_upwards [hε] with t ht
    positivity
  · filter_upwards [hε,hh.eventually (eventually_lt_nhds (by linarith : 0< -Real.log q))] with t ht hbound
    apply div_le_div_of_nonneg_right _ ht.le
    have hd : 0<(growingLVDegree t:ℝ) := by exact_mod_cast growingLVDegree_pos t
    have he : (C+1)*strongScale t≤(-Real.log q)*(growingLVDegree t:ℝ) := by
      apply (div_le_iff₀ hd).mp
      simpa only [mul_div_assoc] using hbound.le
    rw [show q^(growingLVDegree t)=Real.exp ((growingLVDegree t:ℝ)*Real.log q) by
      rw [Real.exp_nat_mul,Real.exp_log hq],←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [he]

theorem weighted_growingMomentDegree_cost (ε : ℝ→ℝ) (b C W : ℝ)
    (hb : 0<b) (_hC : 0≤C)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*strongScale t)*C*Real.sqrt t*b^(growingLVDegree t)/(t*ε t)) atTop (𝓝 0) := by
  have hF := (growingLVDegree_div_log_tendsto.const_mul (Real.log b)).add
    (strongScale_div_log.const_mul W)
  have hh := (sqrt_geometric_cost_tendsto ε
    (fun t => Real.log b*(growingLVDegree t:ℝ)+W*strongScale t) hε hproduct
    (by simpa only [mul_zero,add_zero,add_div,mul_div_assoc] using hF)).const_mul C
  simp only [mul_zero] at hh
  convert hh using 1
  funext t
  rw [Real.exp_add,mul_comm (Real.log b),Real.exp_nat_mul,Real.exp_log hb]
  ring

#print axioms growingLVDegree_exp_lower
#print axioms strongScale_div_degree
#print axioms slow_exponential_div_width
#print axioms strong_exponential_div_width
#print axioms strongScale_div_log
#print axioms weighted_growingMomentDegree_decay
#print axioms weighted_growingMomentDegree_cost
end QuantitativeMaass.Strong

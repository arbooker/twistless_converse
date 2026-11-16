module

public import QuantitativeMaassStrongMomentScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace QuantitativeMaass.Strong

/-- The deeper LV degree pays for a whole outer band and Newton coefficient
costs, while its exponential geometric cost is still subpolynomial in t. -/
def deepLVDegree (t : ℝ) : ℕ := ⌈Real.exp ((4:ℝ)^rawBlockHorizon t)⌉₊^2

theorem deepLVDegree_pos (t : ℝ) : 0<deepLVDegree t := by
  have hp : 0<⌈Real.exp ((4:ℝ)^rawBlockHorizon t)⌉₊ := Nat.ceil_pos.mpr (Real.exp_pos _)
  unfold deepLVDegree
  positivity

theorem sqrt_deepLVDegree (t : ℝ) :
    Real.sqrt (deepLVDegree t:ℝ)=(⌈Real.exp ((4:ℝ)^rawBlockHorizon t)⌉₊:ℝ) := by
  simp only [deepLVDegree,Nat.cast_pow]
  exact Real.sqrt_sq (Nat.cast_nonneg _)

theorem deepLVDegree_bound (t : ℝ) :
    (deepLVDegree t:ℝ)≤4*Real.exp (2*(4:ℝ)^rawBlockHorizon t) := by
  have he : 1≤Real.exp ((4:ℝ)^rawBlockHorizon t) := Real.one_le_exp (by positivity)
  have hc := (Nat.ceil_lt_add_one (Real.exp_pos ((4:ℝ)^rawBlockHorizon t)).le).le
  have hb : (⌈Real.exp ((4:ℝ)^rawBlockHorizon t)⌉₊:ℝ)≤2*Real.exp ((4:ℝ)^rawBlockHorizon t) := by linarith
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg _) hb 2
  simpa only [deepLVDegree,Nat.cast_pow,mul_pow,show (2:ℝ)^2=4 by norm_num,
    ←Real.exp_nat_mul,Nat.cast_ofNat] using hh

theorem deepLVDegree_div_log :
    Tendsto (fun t : ℝ => (deepLVDegree t:ℝ)/Real.log t) atTop (𝓝 0) := by
  have hh := (rawBlockHorizon_log_cost 2 (by norm_num)).const_mul 4
  simp only [mul_zero] at hh
  apply squeeze_zero' _ _ hh
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with t ht
    positivity
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with t ht
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right (deepLVDegree_bound t) ht.le

theorem strongScale_div_rawHorizon :
    Tendsto (fun t : ℝ => strongScale t/(4:ℝ)^rawBlockHorizon t) atTop (𝓝 0) := by
  have hh := ((isLittleO_pow_exp_pos_mul_atTop 2 (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp
    slowScale_tendsto).const_mul 4
  simp only [Function.comp_apply,mul_zero] at hh
  have heq (t : ℝ) : (1/2:ℝ)*slowScale t=slowScale t/2 := by ring
  simp only [heq] at hh
  change Tendsto (fun t => 4*(strongScale t/Real.exp (slowScale t/2))) atTop (𝓝 0) at hh
  apply squeeze_zero' (Eventually.of_forall (fun t => div_nonneg (sq_nonneg _) (by positivity))) _ hh
  filter_upwards [] with t
  have hd : 0<(4:ℝ)^rawBlockHorizon t := by positivity
  have he := mul_le_mul_of_nonneg_left (rawBlockHorizon_lower t) (sq_nonneg (slowScale t))
  rw [show 4*(strongScale t/Real.exp (slowScale t/2))=(4*strongScale t)/Real.exp (slowScale t/2) by ring]
  apply (div_le_div_iff₀ hd (Real.exp_pos _)).mpr
  dsimp only [strongScale]
  nlinarith only [he]

/-- The square-root deficit pays for every exponential cost on the squared
triple-logarithmic scale, including an outer band of that size. -/
theorem deepLV_inverse_sqrt_decay (ε : ℝ→ℝ) (W : ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*strongScale t)/(Real.sqrt (deepLVDegree t:ℝ)*ε t)) atTop (𝓝 0) := by
  have hm := strongScale_div_rawHorizon.const_mul (W+1)
  simp only [mul_zero] at hm
  apply squeeze_zero' _ _ (strong_exponential_div_width ε hε hproduct)
  · filter_upwards [hε] with t he
    positivity
  · filter_upwards [hε,hm.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with t he ht
    have hd : 0<(4:ℝ)^rawBlockHorizon t := by positivity
    have hcost : (W+1)*strongScale t≤(4:ℝ)^rawBlockHorizon t := by
      have hh := (div_le_one hd).mp (show (W+1)*strongScale t/(4:ℝ)^rawBlockHorizon t≤1 by
        simpa only [mul_div_assoc] using ht.le)
      exact hh
    rw [div_mul_eq_div_div]
    apply div_le_div_of_nonneg_right _ he.le
    have hs : 0<Real.sqrt (deepLVDegree t:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast deepLVDegree_pos t)
    apply (div_le_iff₀ hs).mpr
    calc
      _ ≤ Real.exp (-strongScale t)*Real.exp ((4:ℝ)^rawBlockHorizon t) := by
        rw [←Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith only [hcost]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        rw [sqrt_deepLVDegree]
        exact Nat.le_ceil _

theorem deepLV_geometric_decay (ε : ℝ→ℝ) (B W : ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.sqrt t*Real.exp (B*(deepLVDegree t:ℝ)+W*strongScale t)/(t*ε t))
      atTop (𝓝 0) := by
  apply sqrt_geometric_cost_tendsto ε _ hε hproduct
  have hh := (deepLVDegree_div_log.const_mul B).add (strongScale_div_log.const_mul W)
  simpa only [mul_zero,add_zero,add_div,mul_div_assoc] using hh

#print axioms deepLVDegree_pos
#print axioms sqrt_deepLVDegree
#print axioms deepLVDegree_bound
#print axioms deepLVDegree_div_log
#print axioms strongScale_div_rawHorizon
#print axioms deepLV_inverse_sqrt_decay
#print axioms deepLV_geometric_decay
end QuantitativeMaass.Strong

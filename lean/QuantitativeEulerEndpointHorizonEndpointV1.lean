module

public import QuantitativeEulerEndpointCommonAnalyticScaleV1
public import QuantitativeEulerEndpointSubcornerScaledTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointHorizon
open Filter QuantitativeHolomorphic QuantitativeEulerEndpointTraceMass

/-- Removing approximate-invariance loss preserves the exact leading term. -/
theorem remove_factor {x α E δ : ℝ} (hα : 0≤α) (hE : 0≤E) (hδ : 0≤δ) (hδ' : δ≤1/2)
    (hx : (1-δ)*x≤α+E) : x≤α+2*E+2*δ*α := by
  by_cases hh : x≤α
  · nlinarith [mul_nonneg hδ hα]
  · have hp : 0≤x-α := by linarith
    have hm := mul_le_mul_of_nonneg_right hδ' hp
    nlinarith

/-- A genuine geometric horizon bound gives the endpoint inverse log-log
rate. The coefficient of the leading term is preserved exactly. -/
theorem eventual_endpoint_of_horizon_bound (f : ℕ → ℝ) (α C D : ℝ)
    (hα : 0≤α) (hC : 0≤C) (hD : 0≤D)
    (hbound : ∀ n h : ℕ,∀ c : ℝ,0<h →
      1≤Real.log (observationScale c (h+1)) →
      32≤Real.log (Real.log (h+1:ℝ)) →
      (4:ℝ)^n≤(Real.log (observationScale c (h+1)))^2 → D*c^2≤1/2 →
      (1-2/(4:ℝ)^n)*f h≤α+C/(4:ℝ)^n+3*Real.exp (-Real.log (h+1:ℝ)/4)) :
    ∃ B : ℝ,0≤B ∧ ∀ᶠ h : ℕ in atTop,f h≤α+B/Real.log (Real.log (h+1:ℝ)) := by
  obtain ⟨c,hc,hscale⟩ := exists_scale_constant hD
  let B := (2*C+4*α)*4/c^2+6
  have hB : 0≤B := by dsimp only [B]; positivity
  refine ⟨B,hB,?_⟩
  have hc2 : 0<c^2 := sq_pos_of_pos hc
  have hL : Tendsto (fun h : ℕ => Real.log (Real.log (h+1:ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))
  filter_upwards [hL.eventually (eventually_ge_atTop (max 32 (16/c^2))),eventually_ge_atTop 1] with h hlarge hh
  let L := Real.log (Real.log (h+1:ℝ))
  let X := (Real.log (observationScale c (h+1)))^2
  have hlog : 32≤L := (le_max_left _ _).trans hlarge
  have hLp : 0<L := by linarith
  have hXeq : X=c^2*L := log_observationScale_sq c (h+1:ℝ) hLp.le
  have hX : 16≤X := by
    rw [hXeq]
    exact (div_le_iff₀ hc2).mp ((le_max_right _ _).trans hlarge) |>.trans_eq (mul_comm _ _)
  have hs0 : 0≤Real.log (observationScale c (h+1)) := by rw [log_observationScale]; positivity
  have hs : 1≤Real.log (observationScale c (h+1)) := by dsimp only [X] at hX; nlinarith
  obtain ⟨n,hn,hnext⟩ := exists_nat_pow_near (show 1≤X by linarith) (by norm_num : (1:ℝ)<4)
  rw [pow_succ] at hnext
  let R : ℝ := (4:ℝ)^n
  have hR : 4≤R := by dsimp only [R]; nlinarith
  have hR0 : 0<R := by linarith
  have hri : 1/R≤4/X := (div_le_div_iff₀ hR0 (by linarith : 0<X)).mpr (by dsimp only [R]; nlinarith)
  have hb := hbound n h c (by omega) hs hlog hn hscale
  have hp : Real.exp (-Real.log (h+1:ℝ)/4)≤1/L := by
    have he := power_saving_le_loglog (δ:=1) (by exact_mod_cast (show 1<h+1 by omega))
      (by linarith : 16≤Real.log (Real.log (h+1:ℝ))) le_rfl
    simpa only [neg_mul,Real.rpow_neg_one,one_div] using he
  have hδ : 2/R≤1/2 := (div_le_iff₀ hR0).mpr (by linarith)
  have he := remove_factor hα (show 0≤C/R+3*Real.exp (-Real.log (h+1:ℝ)/4) by positivity)
    (show 0≤2/R by positivity) hδ (by simpa only [add_assoc] using hb)
  have hcoef : 0≤2*C+4*α := by positivity
  have hm := mul_le_mul_of_nonneg_left hri hcoef
  have hfinal : (2*C+4*α)*(4/X)+6*(1/L)=B/L := by rw [hXeq]; dsimp only [B]; field_simp
  change f h≤α+B/L
  simp only [div_eq_mul_inv] at he hm hp hfinal ⊢
  nlinarith only [he,hm,hp,hfinal]

#print axioms remove_factor
#print axioms eventual_endpoint_of_horizon_bound
end QuantitativeEulerEndpointHorizon

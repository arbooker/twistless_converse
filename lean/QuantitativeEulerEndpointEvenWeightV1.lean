module

public import QuantitativeEulerEndpointHorizonEndpointV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointHorizon
open Filter AsymptoticSectorComparison

theorem loglog_double_le {x : ℝ} (hx : 2≤x) (hL : 1≤Real.log (Real.log x)) :
    0<Real.log (Real.log (2*x)) ∧ Real.log (Real.log (2*x))≤2*Real.log (Real.log x) := by
  have hx0 : 0<x := by linarith
  have hlx : 0<Real.log x := Real.log_pos (by linarith)
  have htwo : Real.log (2:ℝ)≤Real.log x := Real.log_le_log (by norm_num) hx
  have hinner : Real.log (2*x)≤2*Real.log x := by rw [Real.log_mul (by norm_num) hx0.ne']; linarith
  have hmono : Real.log (Real.log x)≤Real.log (Real.log (2*x)) :=
    Real.log_le_log hlx (Real.log_le_log hx0 (by linarith))
  refine ⟨by linarith,?_⟩
  have hh := Real.log_le_log (Real.log_pos (by linarith : (1:ℝ)<2*x)) hinner
  rw [Real.log_mul (by norm_num) hlx.ne'] at hh
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

/-- Reindex the endpoint estimate at k=2(h+1) and retain the inverse-log-log rate. -/
theorem endpoint_upper_of_even_index (v : ℕ → ℝ) (α B : ℝ) (hB : 0≤B)
    (hv : ∀ᶠ h : ℕ in atTop,v (2*(h+1))/(2*h+2:ℝ)≤α+B/Real.log (Real.log (h+1:ℝ))) :
    ∀ᶠ k : ℕ in evenWeights,v k≤α*(k:ℝ)+(2*B)*(k:ℝ)/Real.log (Real.log (k:ℝ)) := by
  have hL : Tendsto (fun h : ℕ => Real.log (Real.log (h+1:ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))
  have hind : ∀ᶠ h : ℕ in atTop,
      v (2*(h+1))≤α*(2*(h+1):ℕ)+(2*B)*(2*(h+1):ℕ)/Real.log (Real.log (2*(h+1):ℕ)) := by
    filter_upwards [hv,hL.eventually (eventually_ge_atTop 1),eventually_ge_atTop 1] with h hh hlog hh1
    have hx : (2:ℝ)≤h+1 := by exact_mod_cast (show 2≤h+1 by omega)
    have hl := loglog_double_le hx hlog
    have hi : 1/Real.log (Real.log (h+1:ℝ))≤2/Real.log (Real.log (2*(h+1:ℝ))) :=
      (div_le_div_iff₀ (by linarith : 0<Real.log (Real.log (h+1:ℝ))) hl.1).mpr (by simpa using hl.2)
    have hm := mul_le_mul_of_nonneg_left hi (show 0≤B*(2*h+2:ℝ) by positivity)
    have hb := (div_le_iff₀ (by positivity : (0:ℝ)<2*h+2)).mp hh
    norm_num only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] at ⊢
    have he : (2:ℝ)*((h:ℝ)+1)=2*h+2 := by ring
    rw [he] at hi hm ⊢
    simp only [div_eq_mul_inv] at hb hm ⊢
    nlinarith only [hb,hm]
  obtain ⟨H,hH⟩ := eventually_atTop.mp hind
  have he : ∀ᶠ k in evenWeights,Even k := Filter.Eventually.filter_mono inf_le_right (by simp)
  filter_upwards [(eventually_ge_atTop (2*(H+1))).filter_mono inf_le_left,he] with k hk heven
  obtain ⟨l,hl⟩ := heven
  have hh : H≤l-1 := by omega
  have hke : 2*((l-1)+1)=k := by omega
  simpa only [hke] using hH (l-1) hh

#print axioms loglog_double_le
#print axioms endpoint_upper_of_even_index
end QuantitativeEulerEndpointHorizon

module

public import QuantitativeMaassRawCommonTraceEndpointV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeMaass

theorem metric_horizon_trace_error {D K : ℝ} (hD : 0≤D) (hK : 0≤K) (n : ℕ) :
    D/(4:ℝ)^n+4*(((2^n:ℕ):ℝ)+1)/(4:ℝ)^n+
      (12*((2^n:ℕ):ℝ)+13)*K*(2/(4:ℝ)^n)≤(D+8+50*K)/(2:ℝ)^n := by
  have hx : 0<(2:ℝ)^n := by positivity
  have h1 : 1≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
  have hid : (4:ℝ)^n=((2:ℝ)^n)^2 := by rw [pow_two,←mul_pow]; norm_num
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  rw [hid]
  apply (le_div_iff₀ hx).mpr
  field_simp
  nlinarith [mul_nonneg hD (sub_nonneg.mpr h1),mul_nonneg hK (sub_nonneg.mpr h1)]

/-- Degree 2^n balances source recovery and the already available 4^-n
regular approximation, within the same arithmetic horizon. -/
theorem metric_horizon_source_error {K B γ : ℝ} (hK : 0≤K) (hB : 0≤B) (hγ : 0<γ)
    (n : ℕ) :
    K/(γ*((((2*(2^n):ℕ):ℝ))+1))+3*K*(3/(4:ℝ)^n)*B≤
      (K/γ+9*K*B)/(2:ℝ)^n := by
  have hx : 0<(2:ℝ)^n := by positivity
  have h1 : 1≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
  have hid : (4:ℝ)^n=((2:ℝ)^n)^2 := by rw [pow_two,←mul_pow]; norm_num
  have hden : γ*(2*(2:ℝ)^n+1)≥γ*(2:ℝ)^n := by nlinarith
  have hfirst : K/(γ*(2*(2:ℝ)^n+1))≤(K/γ)/(2:ℝ)^n := by
    rw [div_div]
    exact div_le_div_of_nonneg_left hK (mul_pos hγ hx) hden
  have hsecond : 3*K*(3/(4:ℝ)^n)*B≤(9*K*B)/(2:ℝ)^n := by
    rw [hid]
    have hpow : (2:ℝ)^n≤((2:ℝ)^n)^2 := by nlinarith
    have hh := div_le_div_of_nonneg_left (show 0≤9*K*B by positivity) hx hpow
    convert hh using 1
    ring
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  exact (add_le_add hfirst hsecond).trans_eq (by ring)

#print axioms metric_horizon_trace_error
#print axioms metric_horizon_source_error
end QuantitativeMaass

module

public import QuantitativeEulerEndpointWidePacketBoundsV1
public import QuantitativeEulerEndpointNormalizedThresholdV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared

/-- A polynomial bound for the explicit norm of an ORIGINAL packet row.
All geometric parameters and the reciprocal lower height are bounded by U.
The exponent retains the dependence on the weight parameter t. -/
theorem widePacketBound_polynomial (N q : ℕ) (w : ℂ) (R Y H U : ℝ) (t : ℕ)
    (hU : 1≤U) (hN : (N:ℝ)≤U) (hq : (q:ℝ)≤U) (hw : ‖w‖≤U)
    (hR0 : 0≤R) (hR : R≤U) (hH0 : 0≤H) (hH : H≤U)
    (hY : 0<Y) (hYinv : (min 1 Y)⁻¹≤U) :
    widePacketBound N q w R Y H t≤72*9^t*U^(9+10*t) := by
  have hU0 : 0≤U := by linarith
  have hB0 : (0:ℝ)≤(N*q^3:ℕ) := by positivity
  have hB : ((N*q^3:ℕ):ℝ)≤U^4 := by
    push_cast
    calc
      _ ≤ U*U^3 := mul_le_mul hN (pow_le_pow_left₀ (by positivity) hq 3) (by positivity) hU0
      _ = _ := by ring
  have hsum0 : 0≤H+R+1 := by positivity
  have hsum : H+R+1≤3*U := by linarith
  have hb : ((N*q^3:ℕ):ℝ)*(H+R+1)≤3*U^5 := by
    calc
      _ ≤ U^4*(3*U) := mul_le_mul hB hsum hsum0 (by positivity)
      _ = _ := by ring
  have hmin : 0<min 1 Y := lt_min (by norm_num) hY
  have harg0 : 0≤((N*q^3:ℕ):ℝ)*(H+R+1)/min 1 Y := by positivity
  have harg : ((N*q^3:ℕ):ℝ)*(H+R+1)/min 1 Y≤3*U^6 := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ (3*U^5)*U := mul_le_mul hb hYinv (inv_nonneg.mpr hmin.le) (by positivity)
      _ = _ := by ring
  have hceil : (wideCompactCutoff (N*q^3:ℕ) R Y H:ℝ)≤4*U^6 := by
    have hh := (Nat.ceil_lt_add_one harg0).le
    change (wideCompactCutoff (N*q^3:ℕ) R Y H:ℝ)≤_ at hh
    have hpow : 1≤U^6 := one_le_pow₀ hU
    linarith
  have hfold : 2*(wideCompactCutoff (N*q^3:ℕ) R Y H:ℝ)+1≤9*U^6 := by
    have hpow : 1≤U^6 := one_le_pow₀ hU
    linarith
  have hdist : wideDistortion (N*q^3:ℕ) R H≤9*U^10 := by
    apply max_le
    · have hh : 1≤U^10 := one_le_pow₀ hU
      linarith
    · calc
        _ ≤ (3*U^5)^2 := pow_le_pow_left₀ (mul_nonneg hB0 hsum0) hb 2
        _ = _ := by ring
  have hfront : 4*(q:ℝ)^2*(1+‖w‖)≤8*U^3 := by
    calc
      _ ≤ (4*U^2)*(2*U) := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq 2) (by norm_num))
        (by linarith) (by positivity) (by positivity)
      _ = _ := by ring
  have htail : (2*(wideCompactCutoff (N*q^3:ℕ) R Y H:ℝ)+1)*
      (wideDistortion (N*q^3:ℕ) R H)^t≤(9*U^6)*(9*U^10)^t :=
    mul_le_mul hfold (pow_le_pow_left₀ (wideDistortion_pos _ _ _).le hdist t)
      (pow_nonneg (wideDistortion_pos _ _ _).le _) (by positivity)
  have hd0 := (wideDistortion_pos (N*q^3:ℕ) R H).le
  unfold widePacketBound
  calc
    _ ≤ (8*U^3)*((9*U^6)*(9*U^10)^t) := mul_le_mul hfront htail (by positivity) (by positivity)
    _ = _ := by rw [mul_pow,←pow_mul,pow_add]; ring

#print axioms widePacketBound_polynomial
end QuantitativeEulerEndpointPrepared

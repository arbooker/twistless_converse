module

public import QuantitativeEulerEndpointWideBaselineBoundsV1
public import QuantitativeEulerEndpointWideGrowthV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared

theorem wideRowBound_polynomial (B R Y H U : ℝ) (t : ℕ)
    (hU : 1≤U) (hB0 : 0≤B) (hB : B≤U^4)
    (hR0 : 0≤R) (hR : R≤U) (hH0 : 0≤H) (hH : H≤U)
    (hY : 0<Y) (hYinv : (min 1 Y)⁻¹≤U) :
    wideRowBound B R Y H t≤9*9^t*U^(6+10*t) := by
  have hU0 : 0≤U := by linarith
  have hsum0 : 0≤H+R+1 := by positivity
  have hsum : H+R+1≤3*U := by linarith
  have hb : B*(H+R+1)≤3*U^5 := by
    calc
      _ ≤ U^4*(3*U) := mul_le_mul hB hsum hsum0 (by positivity)
      _ = _ := by ring
  have hmin : 0<min 1 Y := lt_min (by norm_num) hY
  have harg0 : 0≤B*(H+R+1)/min 1 Y := by positivity
  have harg : B*(H+R+1)/min 1 Y≤3*U^6 := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ (3*U^5)*U := mul_le_mul hb hYinv (inv_nonneg.mpr hmin.le) (by positivity)
      _ = _ := by ring
  have hceil : (wideCompactCutoff B R Y H:ℝ)≤4*U^6 := by
    have hh := (Nat.ceil_lt_add_one harg0).le
    change (wideCompactCutoff B R Y H:ℝ)≤_ at hh
    have hpow : 1≤U^6 := one_le_pow₀ hU
    linarith
  have hfold : 2*(wideCompactCutoff B R Y H:ℝ)+1≤9*U^6 := by
    have hpow : 1≤U^6 := one_le_pow₀ hU
    linarith
  have hdist : wideDistortion B R H≤9*U^10 := by
    apply max_le
    · have hh : 1≤U^10 := one_le_pow₀ hU
      linarith
    · calc
        _ ≤ (3*U^5)^2 := pow_le_pow_left₀ (mul_nonneg hB0 hsum0) hb 2
        _ = _ := by ring
  unfold wideRowBound
  calc
    _ ≤ (9*U^6)*(9*U^10)^t := mul_le_mul hfold
      (pow_le_pow_left₀ (wideDistortion_pos _ _ _).le hdist t)
      (pow_nonneg (wideDistortion_pos _ _ _).le _) (by positivity)
    _ = _ := by rw [mul_pow,←pow_mul,pow_add]; ring

theorem wideTwistBound_polynomial (N q : ℕ) (w : ℂ) (R Y H U : ℝ) (t : ℕ)
    (hU : 1≤U) (hN : (N:ℝ)≤U) (hq : (q:ℝ)≤U) (hw : ‖w‖≤U)
    (hR0 : 0≤R) (hR : R≤U) (hH0 : 0≤H) (hH : H≤U)
    (hY : 0<Y) (hYinv : (min 1 Y)⁻¹≤U) :
    wideTwistBound N q w R Y H t≤36*9^t*U^(8+10*t) := by
  have hU0 : 0≤U := by linarith
  have hB : ((N*q^3:ℕ):ℝ)≤U^4 := by
    push_cast
    calc
      _ ≤ U*U^3 := mul_le_mul hN (pow_le_pow_left₀ (by positivity) hq 3) (by positivity) hU0
      _ = _ := by ring
  have hb := wideRowBound_polynomial (N*q^3:ℕ) R Y H U t hU (by positivity) hB hR0 hR hH0 hH hY hYinv
  have hp : 2*(q:ℝ)*(1+‖w‖)≤4*U^2 := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ)≤2))
      (show 1+‖w‖≤2*U by linarith) (show 0≤1+‖w‖ by positivity) (show 0≤2*U by positivity)
    nlinarith only [hh]
  unfold wideTwistBound
  calc
    _ ≤ (4*U^2)*(9*9^t*U^(6+10*t)) := mul_le_mul hp hb (wideRowBound_nonneg _ _ _ _ _) (by positivity)
    _ = _ := by rw [show 8+10*t=2+(6+10*t) by omega,pow_add]; ring

theorem wideRamifiedBound_polynomial (p : ℕ) (δ : ℂ) (R Y H U : ℝ) (t : ℕ)
    (hU : 1≤U) (hp : (p:ℝ)≤U) (hδ : ‖δ‖≤U)
    (hR0 : 0≤R) (hR : R≤U) (hH0 : 0≤H) (hH : H≤U)
    (hY : 0<Y) (hYinv : (min 1 Y)⁻¹≤U) :
    wideRamifiedBound p δ R Y H t≤36*9^t*U^(8+10*t) := by
  have hU0 : 0≤U := by linarith
  have hU4 : U≤U^4 := by simpa only [pow_one] using pow_le_pow_right₀ hU (by norm_num : 1≤4)
  have hb := wideRowBound_polynomial p R Y H U t hU (by positivity) (hp.trans hU4) hR0 hR hH0 hH hY hYinv
  have hfront : ((p:ℝ)+1)*(1+‖δ‖)≤4*U^2 := by
    have hh := mul_le_mul (show (p:ℝ)+1≤2*U by linarith)
      (show 1+‖δ‖≤2*U by linarith) (show 0≤1+‖δ‖ by positivity) (show 0≤2*U by positivity)
    nlinarith only [hh]
  unfold wideRamifiedBound
  calc
    _ ≤ (4*U^2)*(9*9^t*U^(6+10*t)) := mul_le_mul hfront hb (wideRowBound_nonneg _ _ _ _ _) (by positivity)
    _ = _ := by rw [show 8+10*t=2+(6+10*t) by omega,pow_add]; ring

#print axioms wideRowBound_polynomial
#print axioms wideTwistBound_polynomial
#print axioms wideRamifiedBound_polynomial
end QuantitativeEulerEndpointPrepared

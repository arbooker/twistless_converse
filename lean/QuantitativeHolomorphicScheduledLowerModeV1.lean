module

public import QuantitativeHolomorphicCutoffScalarBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight AsymptoticCylinderModeComparison

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

def lowerModeCoefficient (P : Parameters A) : ℝ :=
  localizedCoefficient ((AsymptoticReconstructedCount.parameters A P).s+4) (4*Real.pi)+
  slopeCoefficient ((AsymptoticReconstructedCount.parameters A P).s+4) (4*Real.pi)

theorem lowerModeCoefficient_nonneg (P : Parameters A) : 0≤lowerModeCoefficient A P :=
  add_nonneg (localizedCoefficient_nonneg _ (by positivity)) (slopeCoefficient_nonneg _ (by positivity))

def lowerModeGrowthConstant (P : Parameters A) (C : ℝ) : ℝ :=
  2*lowerModeCoefficient A P+|lowerInverseGrowthConstant A P C|+4

theorem lowerModeGrowthConstant_nonneg (P : Parameters A) (C : ℝ) :
    0≤lowerModeGrowthConstant A P C := by
  have ht := lowerModeCoefficient_nonneg A P
  unfold lowerModeGrowthConstant
  positivity

theorem scheduled_lower_mode_error (P : Parameters A) {C s : ℝ} (hC : 0≤C)
    (hs : 1≤s) (d h : ℕ) (hd : (d:ℝ)≤Real.exp (C*s^2)) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let n := newtonDepth A P (2*d+2) (Real.exp (-8*s))
    let Y := lowerCutoff A P (2*d+2) (Real.exp (-8*s)) n
    (2*Real.sqrt (localizedErrorBound (P'.s+4) (4*Real.pi) Y)*
      Real.sqrt (massSlope (P'.s+4) (4*Real.pi) Y))*(Real.sqrt (2*h+2:ℝ))⁻¹≤
      bridgeErrorThird (lowerModeGrowthConstant A P C) (h+1) (Real.exp s) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let n := newtonDepth A P (2*d+2) (Real.exp (-8*s))
  let Y := lowerCutoff A P (2*d+2) (Real.exp (-8*s)) n
  let T := lowerModeCoefficient A P
  let K := |lowerInverseGrowthConstant A P C|
  have hT : 0≤T := lowerModeCoefficient_nonneg A P
  have hK : 0≤K := abs_nonneg _
  have hY : 0<Y := (countFilterError_schedule A P d (Real.exp_pos (-8*s))).2.1
  have hYi : Y⁻¹≤Real.exp (K*s^4) := (growing_lower_inverse A P hC hs d hd).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
  have hE : 1≤Real.exp (K*s^4) := Real.one_le_exp (by positivity)
  have hs4 : 1≤s^4 := by simpa using pow_le_pow_right₀ hs (by norm_num : 0≤4)
  have hcoeff : T*(1+Y⁻¹)≤Real.exp (Real.exp ((2*T+K+4)*s^2)) := by
    calc
      _ ≤ (2*T)*Real.exp (K*s^4) := by nlinarith [mul_le_mul_of_nonneg_left hYi hT,mul_le_mul_of_nonneg_left hE hT]
      _ ≤ Real.exp ((2*T+K)*s^4) := constant_mul_exp_le (by positivity) hs4
      _ ≤ _ := Real.exp_le_exp.mpr (by
        simpa using polynomial_mul_exp_quadratic_le 4 (b:=2*T+K) (C:=0) (by positivity) hs)
  have hlocal := localized_sqrt_product_le (P'.s+4) (by positivity : 0<4*Real.pi) hY
  have hpower := inverse_sqrt_weight_le_trace_power h
  have hh := mul_le_mul (hlocal.trans hcoeff) hpower (by positivity) (Real.exp_nonneg _)
  apply hh.trans_eq
  exact double_exp_mul_trace_power _ _ h

#print axioms scheduled_lower_mode_error

end QuantitativeHolomorphic.Schedule

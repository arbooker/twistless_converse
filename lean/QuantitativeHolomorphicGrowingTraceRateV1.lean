module

public import QuantitativeHolomorphicGrowingGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

theorem polynomial_double_exp_le (m : ℕ) {c K s : ℝ} (hc : 0≤c)
    (hK : 0≤K) (hs : 1≤s) :
    c*(Real.exp (Real.exp (K*s^2)))^m≤Real.exp (Real.exp ((c+m+K)*s^2)) := by
  have hE : 1≤Real.exp (K*s^2) := Real.one_le_exp (by positivity)
  have hcE : c≤Real.exp c := by linarith [Real.add_one_le_exp c]
  have hs2 : 1≤s^2 := by nlinarith
  calc
    _ ≤ Real.exp c*(Real.exp (Real.exp (K*s^2)))^m :=
      mul_le_mul_of_nonneg_right hcE (by positivity)
    _ = Real.exp (c+(m:ℝ)*Real.exp (K*s^2)) := by rw [←Real.exp_nat_mul,←Real.exp_add]
    _ ≤ Real.exp ((c+m)*Real.exp (K*s^2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hE hc]
    _ ≤ _ := Real.exp_le_exp.mpr
      (constant_mul_exp_le (c:=c+m) (a:=K) (by positivity) hs2)

theorem double_exp_mul_trace_power (K s : ℝ) (h : ℕ) :
    Real.exp (Real.exp (K*s^2))*(h+1:ℝ)^(-(1/3:ℝ))=
      bridgeErrorThird K (h+1) (Real.exp s) := by
  rw [Real.rpow_def_of_pos (by positivity : (0:ℝ)<h+1)]
  unfold bridgeErrorThird
  rw [Real.log_exp,←Real.exp_add]
  congr 1
  ring

def geometryGrowthCoefficient : ℝ :=
  (96*periodizationConstant+5+3*Real.pi)/(4*Real.pi)

theorem geometryGrowthCoefficient_nonneg : 0≤geometryGrowthCoefficient := by
  have ht := periodizationConstant_nonneg
  unfold geometryGrowthCoefficient
  positivity

/-- Actual retained trace error, including the infinite periodization tail,
at explicit growing geometric and expression bounds. No error-decay premise. -/
theorem growing_retained_trace_error {D Y H F K s : ℝ} (hD : 0≤D)
    (hY : 0<Y) (hH : 0<H) (hF : 0≤F) (hK : 0≤K) (hs : 1≤s)
    (hDM : D≤Real.exp (Real.exp (K*s^2)))
    (hHM : H≤Real.exp (Real.exp (K*s^2)))
    (hYM : Y⁻¹≤Real.exp (Real.exp (K*s^2)))
    (hFM : F≤Real.exp (Real.exp (K*s^2)))
    (h count : ℕ) (hcount : (count:ℝ)≤Real.exp (Real.exp (K*s^2))) :
    F*uniformRetainedTraceError D Y H h count≤
      bridgeErrorThird (geometryGrowthCoefficient+8+K) (h+1) (Real.exp s) := by
  let M := Real.exp (Real.exp (K*s^2))
  have hM : 1≤M := Real.one_le_exp (Real.exp_nonneg _)
  have hc := tracePowerCoefficient_le_common hD hY hH hM hDM hHM hYM count hcount
  have he := uniformRetainedTraceError_le_power hD hY hH h count
  have hgeom := geometryGrowthCoefficient_nonneg
  have hb : F*(diagonalPowerCoefficient Y H+offDiagonalPowerCoefficient D Y H count)≤
      Real.exp (Real.exp ((geometryGrowthCoefficient+8+K)*s^2)) := by
    calc
      _ ≤ M*(geometryGrowthCoefficient*M^7) := mul_le_mul hFM hc
        (by unfold diagonalPowerCoefficient offDiagonalPowerCoefficient
            have h0 := compactKernelBound_nonneg Y H 0
            have h1 := compactKernelBound_nonneg Y H 1
            positivity) (by positivity)
      _ = geometryGrowthCoefficient*M^8 := by ring
      _ ≤ _ := polynomial_double_exp_le 8 hgeom hK hs
  calc
    _ ≤ F*((diagonalPowerCoefficient Y H+offDiagonalPowerCoefficient D Y H count)*
        (h+1:ℝ)^(-(1/3:ℝ))) := mul_le_mul_of_nonneg_left he hF
    _ = (F*(diagonalPowerCoefficient Y H+offDiagonalPowerCoefficient D Y H count))*
        (h+1:ℝ)^(-(1/3:ℝ)) := by ring
    _ ≤ Real.exp (Real.exp ((geometryGrowthCoefficient+8+K)*s^2))*
        (h+1:ℝ)^(-(1/3:ℝ)) := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := double_exp_mul_trace_power _ _ h

#print axioms growing_retained_trace_error

end QuantitativeHolomorphic.Schedule

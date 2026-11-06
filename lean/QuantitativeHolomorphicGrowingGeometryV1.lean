module

public import QuantitativeHolomorphicGrowingFilterHeightV1
public import QuantitativeHolomorphicThirdPowerScalingV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open AsymptoticUnweightedKernel

def periodizationConstant : ℝ := ∑' n : ℤ, integerDecay n

theorem periodizationConstant_nonneg : 0≤periodizationConstant :=
  tsum_nonneg (fun n => by unfold integerDecay; positivity)

theorem compactKernelBound_le_common {Y H M R : ℝ} (hY : 0<Y) (hH : 0≤H)
    (hM : 1≤M) (hHM : H≤M) (hYM : Y⁻¹≤M) (hR0 : 0≤R) (hR : R≤1) :
    compactKernelBound Y H R≤16*periodizationConstant*M^4 := by
  have hM0 : 0≤M := by linarith
  have hfrac : (R+1)/(2*Y)≤M := by
    calc
      _ ≤ (1+1)/(2*Y) := div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = Y⁻¹ := by field_simp; norm_num
      _ ≤ M := hYM
  have hbase0 : 0≤compactBaseBound Y H R := by unfold compactBaseBound; positivity
  have hbase : compactBaseBound Y H R≤4*M^2 := by
    unfold compactBaseBound
    calc
      _ ≤ 2*M*(1+M) := by gcongr
      _ ≤ 4*M^2 := by nlinarith
  have hp := pow_le_pow_left₀ hbase0 hbase 2
  have ht := periodizationConstant_nonneg
  unfold compactKernelBound
  change compactBaseBound Y H R^2*periodizationConstant≤_
  calc
    _ ≤ (4*M^2)^2*periodizationConstant := mul_le_mul_of_nonneg_right hp ht
    _ = _ := by ring

/-- The actual periodized trace coefficient is polynomial in the common
matrix, strip-height, reciprocal-bottom and finite-periodization bounds. -/
theorem tracePowerCoefficient_le_common {D Y H M : ℝ} (hD : 0≤D)
    (hY : 0<Y) (hH : 0<H) (hM : 1≤M) (hDM : D≤M) (hHM : H≤M)
    (hYM : Y⁻¹≤M) (count : ℕ) (hcount : (count:ℝ)≤M) :
    diagonalPowerCoefficient Y H+offDiagonalPowerCoefficient D Y H count≤
      ((96*periodizationConstant+5+3*Real.pi)/(4*Real.pi))*M^7 := by
  have hM0 : 0≤M := by linarith
  have ht := periodizationConstant_nonneg
  have hK0 := compactKernelBound_le_common hY hH.le hM hHM hYM (by norm_num : (0:ℝ)≤0) (by norm_num)
  have hK1 := compactKernelBound_le_common hY hH.le hM hHM hYM (by norm_num : (0:ℝ)≤1) (by norm_num)
  have hraw : diagonalPowerCoefficient Y H+offDiagonalPowerCoefficient D Y H count≤
      ((16*periodizationConstant*M^4*(1+4*M^2)+1)*M+
        (M*(M^2*(2*Real.pi*M+Real.pi*M^2)+4*M^2*M)+16*periodizationConstant*M^4*M))/(4*Real.pi) := by
    unfold diagonalPowerCoefficient offDiagonalPowerCoefficient
    rw [←add_div]
    simp only [one_div]
    gcongr
  apply hraw.trans
  have h17 : (1:ℝ)≤M^6 := by simpa using pow_le_pow_right₀ hM (by norm_num : 0≤6)
  have h47 : M^4≤M^7 := pow_le_pow_right₀ hM (by norm_num)
  have h57 : M^5≤M^7 := pow_le_pow_right₀ hM (by norm_num)
  have hM7 : M≤M^7 := by simpa using pow_le_pow_right₀ hM (by norm_num : 1≤7)
  apply (div_le_iff₀ (by positivity : 0<4*Real.pi)).mpr
  have he : ((96*periodizationConstant+5+3*Real.pi)/(4*Real.pi))*M^7*(4*Real.pi)=
      (96*periodizationConstant+5+3*Real.pi)*M^7 := by field_simp
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left h57 ht,
    mul_le_mul_of_nonneg_left h47 Real.pi_pos.le,
    mul_le_mul_of_nonneg_left h57 Real.pi_pos.le]

#print axioms compactKernelBound_le_common
#print axioms tracePowerCoefficient_le_common

end QuantitativeHolomorphic.Schedule

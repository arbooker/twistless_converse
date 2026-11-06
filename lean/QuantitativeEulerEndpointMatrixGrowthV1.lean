module

public import QuantitativeEulerEndpointBaselineRowExpressionV1
public import QuantitativeEulerEndpointBaselineEnvelopeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open QuantitativeArithmetic QuantitativeEulerDensityGenerators

theorem wide_matrix_polynomial (B R Y H U : ℝ)
    (hU : 1≤U) (hB0 : 0≤B) (hB : B≤U^4)
    (hR0 : 0≤R) (hR : R≤U) (hH0 : 0≤H) (hH : H≤U)
    (hY : 0<Y) (hYinv : (min 1 Y)⁻¹≤U) :
    4*(1+(wideCompactCutoff B R Y H:ℝ))*B≤36*U^10 := by
  have hrow : 2*(wideCompactCutoff B R Y H:ℝ)+1≤9*U^6 := by
    simpa [wideRowBound] using wideRowBound_polynomial B R Y H U 0 hU hB0 hB hR0 hR hH0 hH hY hYinv
  have hcut : 1+(wideCompactCutoff B R Y H:ℝ)≤9*U^6 := by
    have hh : (0:ℝ)≤(wideCompactCutoff B R Y H:ℝ) := Nat.cast_nonneg _
    linarith
  have hU0 : 0≤U := by linarith
  calc
    _ ≤ (4*(9*U^6))*U^4 := mul_le_mul (mul_le_mul_of_nonneg_left hcut (by norm_num)) hB hB0 (by positivity)
    _ = _ := by ring

theorem baseline_matrix_size_bound (N : ℕ) [NeZero N] {U : ℝ} (hU : 1≤U)
    (hN : (N:ℝ)≤U) (hsize : ∀ i,(baselineSize N i:ℝ)≤U) (i : NewBaselineIndex N) :
    (baselineMatrixSize N i:ℝ)≤U^4 := by
  have hU0 : 0≤U := by linarith
  have hU4 : U≤U^4 := by simpa only [pow_one] using pow_le_pow_right₀ hU (by norm_num : 1≤4)
  cases i with
  | inl i =>
    cases i with
    | none => exact hN.trans hU4
    | some a =>
      change ((N*(primeLift N a).q^3:ℕ):ℝ)≤U^4
      push_cast
      calc
        _ ≤ U*U^3 := mul_le_mul hN
          (pow_le_pow_left₀ (by positivity) (hsize (.inl (some a))) 3) (by positivity) hU0
        _ = _ := by ring
  | inr p => exact (hsize (.inr p)).trans hU4

theorem baseline_matrix_height_polynomial (N : ℕ) [NeZero N] (R Y H U : ℝ)
    (hU : 1≤U) (hN : (N:ℝ)≤U) (hsize : ∀ i,(baselineSize N i:ℝ)≤U)
    (hR0 : 0≤R) (hR : R≤U) (hH0 : 0≤H) (hH : H≤U)
    (hY : 0<Y) (hYinv : (min 1 Y)⁻¹≤U) (i : NewBaselineIndex N) :
    baselineMatrixHeight N R Y H i≤36*U^10 :=
  wide_matrix_polynomial _ R Y H U hU (by positivity)
    (baseline_matrix_size_bound N hU hN hsize i) hR0 hR hH0 hH hY hYinv

#print axioms wide_matrix_polynomial
#print axioms baseline_matrix_height_polynomial
end QuantitativeEulerEndpointPrepared

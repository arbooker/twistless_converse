module

public import QuantitativeMaassMetricPowerExpressionV1
public import QuantitativeHolomorphicMatrixExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
open AsymptoticFiniteBranch QuantitativeHolomorphic
namespace QuantitativeMaass

/-- Common normalization prevents the metric from increasing the base
coefficient mass before the power is taken. -/
theorem metricPowerExpression_mass_le (D F : Expression) (m : ℕ) :
    expressionBound (metricPowerExpression D F m)≤1+(1+expressionBound F)^m := by
  rw [metricPowerExpression_mass]
  have hc := expressionMetricScale_bound D (expressionBound_nonneg D) le_rfl
  have hp := mul_le_mul_of_nonneg_right hc (expressionBound_nonneg F)
  simp only [one_mul] at hp
  apply add_le_add le_rfl
  apply pow_le_pow_left₀
  · have hg := (expressionMetricScale_pos D).le
    have hf := expressionBound_nonneg F
    have hd := expressionBound_nonneg D
    positivity
  · linarith

theorem metricPositiveExpression_matrix (D F : Expression) {B C : ℝ}
    (hB : 0≤B) (hC : 0≤C) (hD : ExpressionMatrixBound D C) (hF : ExpressionMatrixBound F B) :
    ExpressionMatrixBound (metricPositiveExpression D F) (4*C^2*B) := by
  have hh := (hD.compose (hF.compose hD.adjoint hC) (by positivity)).scale (expressionMetricScale D:ℂ)
  have he : 2*C*(2*B*C)=4*C^2*B := by ring
  rw [he] at hh
  exact hh

/-- Explicit integer-matrix height for the very same finite metric filter. -/
theorem metricPowerExpression_matrix (D F : Expression) {B C : ℝ}
    (hB : 1≤B) (hC : 1≤C) (hD : ExpressionMatrixBound D C) (hF : ExpressionMatrixBound F B)
    (m : ℕ) : ExpressionMatrixBound (metricPowerExpression D F m) ((8*C^2*B)^m) := by
  have hb := zero_le_one.trans hB
  have hc := zero_le_one.trans hC
  have hG := metricPositiveExpression_matrix D F hb hc hD hF
  have hc2 : 1≤C^2 := one_le_pow₀ hC
  have hbase : 1≤4*C^2*B := by nlinarith [mul_le_mul hc2 hB (by norm_num : (0:ℝ)≤1) (sq_nonneg C)]
  have hstep := expressionMatrixBound_identity.append (hG.scale (-1))
  rw [max_eq_right hbase] at hstep
  have hp := hstep.power (by positivity : 0≤4*C^2*B) m
  have he : 2*(4*C^2*B)=8*C^2*B := by ring
  rw [he] at hp
  have hpow : 1≤(8*C^2*B)^m := one_le_pow₀ (by nlinarith only [hbase])
  have hh := expressionMatrixBound_identity.append (hp.scale (-1))
  rw [max_eq_right hpow] at hh
  exact hh

#print axioms metricPowerExpression_mass_le
#print axioms metricPositiveExpression_matrix
#print axioms metricPowerExpression_matrix
end QuantitativeMaass

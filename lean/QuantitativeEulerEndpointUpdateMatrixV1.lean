module

public import QuantitativeEulerEndpointUpdateExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointUpdateExpression
open AsymptoticFiniteBranch QuantitativeHolomorphic Polynomial
open QuantitativeEulerEndpointPolynomialExpression

theorem update_matrix {u a g : Expression} {A G : ℝ} (hA : 1≤A) (hG : 1≤G)
    (hu : ExpressionMatrixBound u 1) (ha : ExpressionMatrixBound a A)
    (hg : ExpressionMatrixBound g G) (n : ℕ) :
    ExpressionMatrixBound (updateExpression u a g n) (8*A^2*(8*A^2*G)^n) := by
  have hA0 : 0≤A := by linarith
  have hG0 : 0≤G := by linarith
  have hAA : 1≤A^2 := one_le_pow₀ hA
  have hAG : 1≤A^2*G := by nlinarith [mul_le_mul hAA hG (by norm_num : (0:ℝ)≤1) (sq_nonneg A)]
  let energy := composeExpression (composeExpression a g) a
  let step := u++scaleExpression (-1) energy
  let cut := u++scaleExpression (-1) (cornerPower u step n)
  have he : ExpressionMatrixBound energy (4*A^2*G) := by
    have h := (ha.compose hg hG0).compose ha hA0
    convert h using 1
    ring
  have hs : ExpressionMatrixBound step (4*A^2*G) :=
    (hu.append (he.scale (-1))).mono (max_le (by linarith) le_rfl)
  have hp : ExpressionMatrixBound (cornerPower u step n) (2*(8*A^2*G)^n) := by
    have h := (hs.power (by positivity) n).compose hu (by norm_num)
    convert h using 1
    · rfl
    · ring
  have hpow : 1≤(8*A^2*G)^n := one_le_pow₀ (by linarith)
  have hc : ExpressionMatrixBound cut (2*(8*A^2*G)^n) :=
    (hu.append (hp.scale (-1))).mono (max_le (by linarith) le_rfl)
  have hsa : ExpressionMatrixBound (composeExpression (composeExpression a cut) a)
      (8*A^2*(8*A^2*G)^n) := by
    have h := (ha.compose hc (by positivity)).compose ha hA0
    convert h using 1
    ring
  have hupper : A≤8*A^2*(8*A^2*G)^n := by
    have hAA' : A≤A^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hpow (sq_nonneg A)
    nlinarith
  exact (ha.append (hsa.scale (-1))).mono (max_le hupper le_rfl)

theorem sharpened_matrix {u a g : Expression} {A G : ℝ} (hA : 1≤A) (hG : 1≤G)
    (hu : ExpressionMatrixBound u 1) (ha : ExpressionMatrixBound a A)
    (hg : ExpressionMatrixBound g G) (n : ℕ) (q : ℝ[X]) :
    ExpressionMatrixBound (sharpenedExpression u a g n q)
      (2*(16*A^2*(8*A^2*G)^n)^q.natDegree) := by
  have hA0 : 0≤A := by linarith
  have hG0 : 0≤G := by linarith
  have hAA : 1≤A^2 := one_le_pow₀ hA
  have hAG : 1≤A^2*G := by nlinarith [mul_le_mul hAA hG (by norm_num : (0:ℝ)≤1) (sq_nonneg A)]
  have hpow : 1≤(8*A^2*G)^n := one_le_pow₀ (by linarith)
  have hbound : 1≤8*A^2*(8*A^2*G)^n := by
    nlinarith [mul_le_mul hAA hpow (by norm_num : (0:ℝ)≤1) (sq_nonneg A)]
  have h := corner_matrix (by positivity : 0≤8*A^2*(8*A^2*G)^n) (by norm_num)
    (update_matrix hA hG hu ha hg n) hu q
  rw [max_eq_right hbound,mul_one] at h
  convert h using 1
  · rfl
  · ring

#print axioms update_matrix
#print axioms sharpened_matrix
end QuantitativeEulerEndpointUpdateExpression

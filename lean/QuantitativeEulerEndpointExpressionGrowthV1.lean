module

public import QuantitativeEulerEndpointUpdateMatrixV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointExpressionGrowth
open AsymptoticFiniteBranch QuantitativeHolomorphic Polynomial
open QuantitativeEulerEndpointUpdateExpression

/-- A single natural exponent accounts for both coefficient mass and
matrix height under one sharpened update. -/
def stepExponent (r L d : ℕ) : ℕ := 8*(d+1)*(L+1)*r

theorem exponent_le {r : ℕ} (hr : 1≤r) (L d : ℕ) :
    1+(2*r+1+(2*r+2)*L)*d≤stepExponent r L d := by
  have h1 : 1≤r*(L+1)*(d+1) := by
    have hL : 1≤L+1 := by omega
    have hd : 1≤d+1 := by omega
    nlinarith [Nat.mul_le_mul hr hL, Nat.mul_le_mul (Nat.mul_le_mul hr hL) hd]
  have h2 : 2*r+1+(2*r+2)*L≤4*r*(L+1) := by nlinarith
  have h3 := Nat.mul_le_mul_right d h2
  unfold stepExponent
  nlinarith

theorem power_step {B : ℝ} (hB : 16≤B) {r : ℕ} (hr : 1≤r) (L d : ℕ) :
    B*(16*(B^r)^2*(8*(B^r)^2*B)^L)^d≤B^(stepExponent r L d) := by
  have hB0 : 0≤B := by linarith
  have hB1 : 1≤B := by linarith
  have h1 : 16*(B^r)^2≤B^(2*r+1) := by
    calc
      _ ≤ B*(B^r)^2 := mul_le_mul_of_nonneg_right hB (sq_nonneg _)
      _ = _ := by simp only [pow_add,pow_one,pow_mul]; ring
  have h2 : 8*(B^r)^2*B≤B^(2*r+2) := by
    calc
      _ ≤ B*(B^r)^2*B := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (show 8≤B by linarith) (sq_nonneg _)) hB0
      _ = _ := by simp only [pow_add,pow_mul]; ring
  have h3 : 16*(B^r)^2*(8*(B^r)^2*B)^L≤B^(2*r+1+(2*r+2)*L) := by
    calc
      _ ≤ B^(2*r+1)*(B^(2*r+2))^L := mul_le_mul h1
        (pow_le_pow_left₀ (by positivity) h2 L) (by positivity) (by positivity)
      _ = _ := by simp only [pow_add,pow_mul]
  calc
    _ ≤ B*(B^(2*r+1+(2*r+2)*L))^d := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) h3 d) hB0
    _ = B^(1+(2*r+1+(2*r+2)*L)*d) := by simp only [pow_add,pow_one,pow_mul]
    _ ≤ _ := pow_le_pow_right₀ hB1 (exponent_le hr L d)

theorem sharpened_common_bound {u a g : Expression} {B : ℝ} (hB : 16≤B)
    {r : ℕ} (hr : 1≤r) (hu : expressionBound u≤1)
    (huM : ExpressionMatrixBound u 1)
    (ha : expressionBound a≤B^r) (haM : ExpressionMatrixBound a (B^r))
    (hg : expressionBound g≤B) (hgM : ExpressionMatrixBound g B)
    (L : ℕ) (q : ℝ[X]) (hq : (∑ i∈q.support, |q.coeff i|)≤B) :
    expressionBound (sharpenedExpression u a g L q)≤B^(stepExponent r L q.natDegree) ∧
    ExpressionMatrixBound (sharpenedExpression u a g L q) (B^(stepExponent r L q.natDegree)) := by
  have hB0 : 0≤B := by linarith
  have hB1 : 1≤B := by linarith
  have hA : 1≤B^r := one_le_pow₀ hB1
  have hb := power_step hB hr L q.natDegree
  constructor
  · have hm := sharpened_mass u a g hA hB1 hu ha hg L q
    apply hm.trans (le_trans _ hb)
    apply mul_le_mul hq _ (by positivity) hB0
    apply pow_le_pow_left₀ (by positivity)
    apply mul_le_mul (by nlinarith [sq_nonneg (B^r)]) _ (by positivity) (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [mul_nonneg (sq_nonneg (B^r)) hB0]
  · apply (sharpened_matrix hA hB1 huM haM hgM L q).mono
    exact (mul_le_mul_of_nonneg_right (show 2≤B by linarith) (by positivity)).trans hb

#print axioms exponent_le
#print axioms power_step
#print axioms sharpened_common_bound
end QuantitativeEulerEndpointExpressionGrowth

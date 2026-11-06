module

public import QuantitativeEulerEndpointNormalizedThresholdV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointNormalizedThreshold

/-- Add the baseline bound as the first row of the prime packet. -/
def prepend (D : ℝ) (C : ℕ → ℝ) : ℕ → ℝ
  | 0 => D
  | j+1 => C j

theorem squareSum_prepend (D : ℝ) (C : ℕ → ℝ) (n : ℕ) :
    squareSum (prepend D C) (n+1)=D^2+squareSum C n := by
  unfold squareSum
  rw [Fin.sum_univ_succ]
  rfl

/-- Adding a baseline detector pays only its own logarithmic square bound. -/
theorem prepend_log_cost (D : ℝ) (C : ℕ → ℝ) (n : ℕ) {A : ℝ} (hA : 0≤A) :
    Real.log (2/(QuantitativeEulerEndpointBlockNormalization.factor (prepend D C) (n+1)*threshold A)^2)≤
      Real.log (2/(QuantitativeEulerEndpointBlockNormalization.factor C n*threshold A)^2)+
        2*Real.log (1+D^2) := by
  rw [logarithmic_cost _ _ hA,logarithmic_cost _ _ hA,squareSum_prepend]
  have hpos : 0<1+(D^2+squareSum C n) := by linarith [sq_nonneg D,squareSum_nonneg C n]
  have hprod : 1+(D^2+squareSum C n)≤(1+D^2)*(1+squareSum C n) := by
    nlinarith [mul_nonneg (sq_nonneg D) (squareSum_nonneg C n)]
  have hlog := Real.log_le_log hpos hprod
  rw [Real.log_mul (by positivity : (1+D^2)≠0)
    (by linarith [squareSum_nonneg C n] : (1+squareSum C n)≠0)] at hlog
  linarith

theorem log_square_polynomial {D K U : ℝ} (d : ℕ)
    (hD0 : 0≤D) (_hK0 : 0≤K) (hU : 1≤U) (hD : D≤K*U^d) :
    Real.log (1+D^2)≤Real.log (1+K^2)+(2*(d:ℝ))*Real.log U := by
  have hUpos : 0<U := by linarith
  have hs := pow_le_pow_left₀ hD0 hD 2
  have hone : 1≤U^(2*d) := one_le_pow₀ hU
  have hh : 1+D^2≤(1+K^2)*U^(2*d) := by
    have he : (K*U^d)^2=K^2*U^(2*d) := by rw [mul_pow,←pow_mul,Nat.mul_comm d 2]
    rw [he] at hs
    nlinarith
  have hl := Real.log_le_log (by positivity : 0<1+D^2) hh
  rw [Real.log_mul (by positivity : (1+K^2)≠0) (pow_pos hUpos _).ne',Real.log_pow] at hl
  push_cast at hl
  exact hl

#print axioms squareSum_prepend
#print axioms prepend_log_cost
#print axioms log_square_polynomial
end QuantitativeEulerEndpointNormalizedThreshold

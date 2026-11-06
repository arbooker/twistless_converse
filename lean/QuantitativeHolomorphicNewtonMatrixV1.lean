module

public import QuantitativeHolomorphicMatrixExpressionV1
public import QuantitativeHolomorphicNewtonTransportV1
public import QuantitativeHolomorphicObservationExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open AsymptoticFiniteBranch

/-- Newton inverse-square-root normalization has an explicit common integer
matrix height, independently of its expansion's coefficient count. -/
theorem expressionMatrixBound_inverseSqrt {E : Expression} {B : ℝ}
    (hB : 1 ≤ B) (hE : ExpressionMatrixBound E B) (n : ℕ) :
    ExpressionMatrixBound (inverseSqrtExpression E n) ((8*B)^(4^n)) := by
  let D := 8*B
  have hD : 1 ≤ D := by dsimp [D]; linarith
  induction n with
  | zero => exact expressionMatrixBound_identity.mono (by simpa using hD)
  | succ n ih =>
    let K := D^(4^n)
    have hK : 1 ≤ K := one_le_pow₀ hD
    have hK0 : 0 ≤ K := zero_le_one.trans hK
    have hqq := ih.compose ih hK0
    have heqq : ExpressionMatrixBound
        (composeExpression E (composeExpression (inverseSqrtExpression E n) (inverseSqrtExpression E n)))
        (4*B*K^2) := by
      have hh := hE.compose hqq (by positivity : 0 ≤ 2*K*K)
      convert hh using 1
      ring
    have hBK : 1 ≤ B*K^2 := one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hK)
    have hlarge : 1 ≤ 4*B*K^2 := by nlinarith
    have hs := (expressionMatrixBound_identity.scale 3).append (heqq.scale (-1))
    have hnew := (ih.compose hs (le_trans zero_le_one (le_max_left _ _))).scale (1/2)
    have hbound : 2*K*max 1 (4*B*K^2) ≤ D^(4^(n+1)) := by
      rw [max_eq_right hlarge]
      calc
        _ = D*K^3 := by dsimp only [D]; ring
        _ = D^(1+3*4^n) := by
          rw [pow_add,pow_one,Nat.mul_comm 3 (4^n),pow_mul]
        _ ≤ D^(4^(n+1)) := by
          apply pow_le_pow_right₀ hD
          have hp : 1 ≤ 4^n := Nat.one_le_pow n 4 (by omega)
          rw [pow_succ]
          omega
    exact hnew.mono hbound

/-- Actual Gram normalization costs only the indicated matrix-entry height;
composition and adjugation have been checked against the orbit action. -/
theorem expressionMatrixBound_normalized {E : Expression} {B : ℝ}
    (hB : 1 ≤ B) (hE : ExpressionMatrixBound E B) (n : ℕ) :
    ExpressionMatrixBound (normalizedReconstructionExpression E n)
      (2*B*(16*B^2)^(4^n)) := by
  have hg : ExpressionMatrixBound (composeExpression (adjointExpression E) E) (2*B^2) := by
    have hh := hE.adjoint.compose hE (zero_le_one.trans hB)
    convert hh using 1
    ring
  have hG : 1 ≤ 2*B^2 := by nlinarith [one_le_pow₀ hB (n:=2)]
  have hq := expressionMatrixBound_inverseSqrt hG hg n
  have hh := hE.compose hq (by positivity : 0 ≤ (8*(2*B^2))^(4^n))
  convert hh using 1
  · rfl
  · rw [show 8*(2*B^2)=16*B^2 by ring]

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns AsymptoticCompactObservationCount

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)
variable {ι : Type*}

/-- Matrix complexity of the actual counting filter, reduced to the raw
finite reconstruction and individual observation rows. All Gram, Newton,
adjoint, expansion, and degree costs are proved explicitly. -/
theorem countObservationFilterExpression_matrix_bound (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (Y : ℝ) (j J n d : ℕ) {R B : ℝ}
    (hR : 0 ≤ R) (hB : 1 ≤ B)
    (hr : ∀ i ∈ qs, ExpressionMatrixBound
      (rowExpression hN (r i) e (hs i)
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+4)) R)
    (hv : ExpressionMatrixBound (scaledCutCountExpression A hN P e Y j J) B) :
    let V : ℝ := 2*B*(16*B^2)^(4^n)
    ExpressionMatrixBound (countObservationFilterExpression A hN P e qs r s hs Y j J n d)
      (4*V^2*(2*max 1 (8*R^2*V^2))^d) :=
  expressionMatrixBound_observationFilter qs _ _ _ hR (by positivity) hr
    (expressionMatrixBound_normalized hB hv n) d

#print axioms expressionMatrixBound_inverseSqrt
#print axioms expressionMatrixBound_normalized
#print axioms countObservationFilterExpression_matrix_bound

end QuantitativeHolomorphic

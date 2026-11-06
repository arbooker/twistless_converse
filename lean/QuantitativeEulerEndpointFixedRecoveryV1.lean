module

public import QuantitativeEulerEndpointFixedCorrectionBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDiamondDecode QuantitativeEulerDiamondPolynomial
open AsymptoticFreshCompactDefects AsymptoticRationalBranches AsymptoticRegularBranchFamily
open AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

/-- Exact recovery groups the two actual correction operators before any
norm estimate. The first term retains the original fixed-prime average. -/
theorem compact_prime_recovery_combined (N ℓ : ℕ) [Fact ℓ.Prime]
    (hN : 0<N) (hℓ : ¬ℓ∣N) (w : ℂ) (j : Fin (ℓ-1))
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    w • compact (matrixBranch N ℓ hN hℓ j) hs hε t x-compact identityBranch hs hε t x=
      compactAction hs hε t x (primeAverage N ℓ hN hℓ w*primeInverse ℓ)-
      compactAction hs hε t x
        (primeCongruenceCorrection N ℓ hN hℓ w j*primeInverse ℓ+
          primePeriodCorrection N ℓ hN hℓ w j*
            Polynomial.aeval (primeX ℓ) (correctionPolynomial ℓ)) := by
  have he := compact_prime_recovery N ℓ hN hℓ w j hs hε t x
  dsimp only at he
  rw [map_add]
  exact he.trans (sub_sub _ _ _)

/-- The fixed-prime individual row is controlled by eighteen times the
original averaged-row energy on a union of translates, plus twice the
literal combined correction energy. The inverse cost is uniformly three. -/
theorem fixed_prime_residual_squared (N ℓ : ℕ) [Fact ℓ.Prime]
    (hN : 0<N) (hℓ : ¬ℓ∣N) (w : ℂ) (j : Fin (ℓ-1))
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    ‖(w • compact (matrixBranch N ℓ hN hℓ j) hs hε t x-
      compact identityBranch hs hε t x) v‖^2≤
      18*‖twist N ℓ hN (Fact.out : ℓ.Prime).pos w (inverseRegion_compact ℓ hs) hε t x v‖^2+
      2*‖compactAction hs hε t x
        (primeCongruenceCorrection N ℓ hN hℓ w j*primeInverse ℓ+
          primePeriodCorrection N ℓ hN hℓ w j*
            Polynomial.aeval (primeX ℓ) (correctionPolynomial ℓ)) v‖^2 := by
  have hinv := compact_prime_inverse_bound ℓ (Fact.out : ℓ.Prime).two_le
    (primeAverage N ℓ hN hℓ w) hs hε t x v
  rw [compactAction_primeAverage,_root_.neg_apply,norm_neg] at hinv
  have hi2 := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (by norm_num : (0 : ℝ)≤3) (norm_nonneg _))).2 hinv
  rw [compact_prime_recovery_combined,_root_.sub_apply]
  have h := norm_sub_le
    (compactAction hs hε t x (primeAverage N ℓ hN hℓ w*primeInverse ℓ) v)
    (compactAction hs hε t x
      (primeCongruenceCorrection N ℓ hN hℓ w j*primeInverse ℓ+
        primePeriodCorrection N ℓ hN hℓ w j*
          Polynomial.aeval (primeX ℓ) (correctionPolynomial ℓ)) v)
  have h2 := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 h
  nlinarith [sq_nonneg
    (‖compactAction hs hε t x (primeAverage N ℓ hN hℓ w*primeInverse ℓ) v‖-
      ‖compactAction hs hε t x
        (primeCongruenceCorrection N ℓ hN hℓ w j*primeInverse ℓ+
          primePeriodCorrection N ℓ hN hℓ w j*
            Polynomial.aeval (primeX ℓ) (correctionPolynomial ℓ)) v‖)]

#print axioms compact_prime_recovery_combined
#print axioms fixed_prime_residual_squared
end QuantitativeEulerEndpointPrepared

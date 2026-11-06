module

public import QuantitativeEulerEndpointRightCongrV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDiamondDecode QuantitativeEulerDiamondPolynomial
open AsymptoticFreshAveraging AsymptoticFreshCompactDefects
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

/-- Exact fixed-prime recovery after any group-ring right multiplier.
All right products are composed before applying geometric norm bounds. -/
theorem compact_prime_recovery_right (N ℓ : ℕ) [Fact ℓ.Prime]
    (hN : 0<N) (hℓ : ¬ℓ∣N) (w : ℂ) (j : Fin (ℓ-1)) (E : Ring)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    compactAction hs hε t x ((w • symbol (defectLabel N ℓ hN hℓ j)-1)*E)=
      compactAction hs hε t x (primeAverage N ℓ hN hℓ w*(primeInverse ℓ*E))-
      compactAction hs hε t x
        (primeCongruenceCorrection N ℓ hN hℓ w j*(primeInverse ℓ*E)+
          primePeriodCorrection N ℓ hN hℓ w j*
            (Polynomial.aeval (primeX ℓ) (correctionPolynomial ℓ)*E)) := by
  let A := w • symbol (defectLabel N ℓ hN hℓ j)-1
  let B := primeAverage N ℓ hN hℓ w*primeInverse ℓ-
    (primeCongruenceCorrection N ℓ hN hℓ w j*primeInverse ℓ+
      primePeriodCorrection N ℓ hN hℓ w j*
        Polynomial.aeval (primeX ℓ) (correctionPolynomial ℓ))
  have h {u : Set ℍ} (hu : IsCompact u) :
      compactAction hu hε t x A=compactAction hu hε t x B := by
    have he := (compact_prime_residual_eq N ℓ hN hℓ j w hu hε t x).trans
      (compact_prime_recovery_combined N ℓ hN hℓ w j hu hε t x)
    exact he.trans (map_sub (compactAction hu hε t x) _ _).symm
  have he := compact_right_multiplier_congr A B E hε t x h hs
  have hBE : B*E=primeAverage N ℓ hN hℓ w*(primeInverse ℓ*E)-
      (primeCongruenceCorrection N ℓ hN hℓ w j*(primeInverse ℓ*E)+
        primePeriodCorrection N ℓ hN hℓ w j*
          (Polynomial.aeval (primeX ℓ) (correctionPolynomial ℓ)*E)) := by
    dsimp only [B]
    rw [sub_mul,add_mul]
    simp only [mul_assoc]
  exact he.trans ((congrArg (compactAction hs hε t x) hBE).trans
    (map_sub (compactAction hs hε t x) _ _))

#print axioms compact_prime_recovery_right
end QuantitativeEulerEndpointPrepared

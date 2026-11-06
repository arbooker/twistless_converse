module

public import QuantitativeEulerEndpointRingTransportV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDiamondDecode QuantitativeEulerDiamondPolynomial
open QuantitativeArithmeticDiamondLabels AsymptoticCongruenceLabels
open AsymptoticFreshAveraging AsymptoticFreshCompactDefects
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

/-- The canonical observed residual is expressed in the original Fricke
and fixed-prime averaged rows plus literal Gamma1 corrections, with every
right multiplier already composed. -/
theorem compact_canonical_recovery_right (N ℓ : ℕ) [Fact ℓ.Prime]
    (hN : 0<N) (hℓ : ¬ℓ∣N) (w : ℂ) (hw : w*w=1) (j : Fin (ℓ-1)) (g : G)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    let E := symbol ((defectLabel N ℓ hN hℓ j)⁻¹*g)
    compactAction hs hε t x
      ((symbol (integralLabel (swappedCanonical N ℓ hℓ j))-1)*symbol g)=
      (-w) • (compactAction hs hε t x (frickeRow N hN w*E)+
        compactAction hs hε t x (primeAverage N ℓ hN hℓ w*(primeInverse ℓ*E))-
        compactAction hs hε t x
          (primeCongruenceCorrection N ℓ hN hℓ w j*(primeInverse ℓ*E)+
            primePeriodCorrection N ℓ hN hℓ w j*
              (Polynomial.aeval (primeX ℓ) (correctionPolynomial ℓ)*E))) := by
  let E := symbol ((defectLabel N ℓ hN hℓ j)⁻¹*g)
  let A := frickeRow N hN w
  let R := w • symbol (defectLabel N ℓ hN hℓ j)-1
  have halg : (symbol (integralLabel (swappedCanonical N ℓ hℓ j))-1)*symbol g=
      (-w) • ((A+R)*E) := by
    dsimp only [A,R,E,frickeRow]
    rw [canonical_residual_identity N ℓ hN hℓ w hw j,smul_mul_assoc,smul_mul_assoc,
      mul_assoc,symbol.map_mul]
  have hsum : compactAction hs hε t x ((A+R)*E)=
      compactAction hs hε t x (A*E)+compactAction hs hε t x (R*E) := by
    rw [add_mul,map_add]
  have hr := compact_prime_recovery_right N ℓ hN hℓ w j E hs hε t x
  have hc := congrArg (fun T : Space →L[ℂ] Space => compactAction hs hε t x (A*E)+T) hr
  have he := (congrArg (compactAction hs hε t x) halg).trans
    ((map_smul (compactAction hs hε t x) (-w) ((A+R)*E)).trans
      (congrArg (fun T : Space →L[ℂ] Space => (-w) • T) (hsum.trans hc)))
  exact he.trans (congrArg (fun T : Space →L[ℂ] Space => (-w) • T) (add_sub_assoc _ _ _).symm)

#print axioms compact_canonical_recovery_right
end QuantitativeEulerEndpointPrepared

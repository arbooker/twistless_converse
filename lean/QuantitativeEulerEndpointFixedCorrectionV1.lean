module

public import QuantitativeEulerEndpointFiniteMultiplierV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane CongruenceSubgroup QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode
open QuantitativeArithmeticDiamondLabels
open AsymptoticCongruenceLabels AsymptoticFreshCompactDefects AsymptoticFreshAveraging
open AsymptoticRegularBranchFamily AsymptoticIntegralSubgroup
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

def fixedCorrectionLetter (N ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ℓ∣N)
    (j : Fin (ℓ-1)) : Option (Fin (ℓ-1)) → SL(2,ℤ)
  | none => defectTranslation N ℓ hℓ j
  | some i => defectDifference N ℓ hℓ i j

theorem fixedCorrectionLetter_mem (N ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ℓ∣N)
    (j : Fin (ℓ-1)) (i : Option (Fin (ℓ-1))) :
    fixedCorrectionLetter N ℓ hℓ j i∈Gamma1 N := by
  cases i with
  | none => exact defectTranslation_mem N ℓ hℓ j
  | some i => exact defectDifference_mem N ℓ hℓ i j

def fixedCorrectionMultiplier (N ℓ : ℕ) [Fact ℓ.Prime] (hN : 0<N) (hℓ : ¬ℓ∣N)
    (E F : Ring) (j : Fin (ℓ-1)) : Option (Fin (ℓ-1)) → Ring
  | none => symbol (defectLabel N ℓ hN hℓ j)*F
  | some i => (symbol (defectLabel N ℓ hN hℓ j)*symbol (primeLabels ℓ i))*E

/-- The two literal diamond-recovery corrections, with arbitrary fixed
right multipliers, form a scalar multiple of a finite family of actual
Gamma1 defects. No congruence invariance is assumed. -/
theorem fixedCorrection_sum (N ℓ : ℕ) [Fact ℓ.Prime] (hN : 0<N) (hℓ : ¬ℓ∣N)
    (E F : Ring) (w : ℂ) (j : Fin (ℓ-1)) :
    primeCongruenceCorrection N ℓ hN hℓ w j*E+
      primePeriodCorrection N ℓ hN hℓ w j*F=
    w • ∑ i : Option (Fin (ℓ-1)),
      (symbol (integralLabel (fixedCorrectionLetter N ℓ hℓ j i))-1)*
        fixedCorrectionMultiplier N ℓ hN hℓ E F j i := by
  rw [Fintype.sum_option]
  simp only [fixedCorrectionLetter,fixedCorrectionMultiplier,primeCongruenceCorrection,
    primePeriodCorrection,Finset.sum_mul,smul_add,Finset.smul_sum,smul_mul_assoc,mul_assoc]
  exact add_comm _ _

theorem compact_fixedCorrection_sum (N ℓ : ℕ) [Fact ℓ.Prime] (hN : 0<N) (hℓ : ¬ℓ∣N)
    (E F : Ring) (w : ℂ) (j : Fin (ℓ-1)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    compactAction hs hε t x (primeCongruenceCorrection N ℓ hN hℓ w j*E+
      primePeriodCorrection N ℓ hN hℓ w j*F) v=
    w • ∑ i : Option (Fin (ℓ-1)), compactAction hs hε t x
      ((symbol (integralLabel (fixedCorrectionLetter N ℓ hℓ j i))-1)*
        fixedCorrectionMultiplier N ℓ hN hℓ E F j i) v := by
  rw [fixedCorrection_sum,map_smul,map_sum,_root_.smul_apply,_root_.sum_apply]

#print axioms fixedCorrectionLetter_mem
#print axioms compact_fixedCorrection_sum
end QuantitativeEulerEndpointPrepared

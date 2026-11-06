module

public import QuantitativeEulerEndpointMultiplierV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeHolomorphic QuantitativeArithmetic
open QuantitativeEulerDiamondDecode QuantitativeArithmeticDiamondLabels
open AsymptoticCongruenceLabels AsymptoticIntegralSubgroup AsymptoticFreshAveraging
open AsymptoticFreshCompactDefects AsymptoticRegularBranchFamily AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)

def differenceCorrectionRegion (j i : Fin (q-1)) (s : Set ℍ) : Set ℍ :=
  translatedMultiplierRegion (defectLabel N q hN hq j*primeLabels q i) q s

theorem differenceCorrectionRegion_compact (j i : Fin (q-1)) {s : Set ℍ}
    (hs : IsCompact s) : IsCompact (differenceCorrectionRegion N q hN hq j i s) :=
  translatedMultiplierRegion_compact _ q hs

def periodCorrectionRegion (j : Fin (q-1)) (s : Set ℍ) : Set ℍ :=
  translatedMultiplierRegion (defectLabel N q hN hq j) q s

theorem periodCorrectionRegion_compact (j : Fin (q-1)) {s : Set ℍ}
    (hs : IsCompact s) : IsCompact (periodCorrectionRegion N q hN hq j s) :=
  translatedMultiplierRegion_compact _ q hs

/-- Fully explicit growing-prime transport for each difference multiplier. -/
theorem difference_correction_polynomial_bound (j i : Fin (q-1)) (A : Ring)
    {s : Set ℍ} (hs : IsCompact s) {ε H : ℝ} (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤1) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x (A*differenceMultiplier N q hN hq j i) v‖≤
      3*((integerCompactDistortion (8*(1+(N : ℝ))^2*(q : ℝ)^4) H)^t*
        ‖compactAction (differenceCorrectionRegion_compact N q hN hq j i hs) hε t x A v‖) := by
  have hi : i.val+1≤q := by have h := i.isLt; omega
  have hM : IntegerAction (defectLabel N q hN hq j*primeLabels q i)
      (defectIntegerMatrix N q hq j*translationIntegerMatrix q (i.val+1)) :=
    (defect_integer_action N q hN hq j).mul
      (translation_label_integer_action q (i.val+1) (Fact.out : q.Prime).pos)
  have hb := matrix_entry_bound_mul (by positivity) (defect_integer_height N q hq j)
    (translation_integer_bound q (i.val+1) hi)
  have hb' : MatrixEntryBound
      (defectIntegerMatrix N q hq j*translationIntegerMatrix q (i.val+1))
      (4*(1+(N : ℝ))^2*(q : ℝ)^3) := by
    convert hb using 1
    ring
  have ht := transported_prime_inverse_bound _ q (Fact.out : q.Prime).two_le hM
    (by positivity) hb' A hs hε hre him t x v
  have ha : A*differenceMultiplier N q hN hq j i=
      (A*symbol (defectLabel N q hN hq j*primeLabels q i))*primeInverse q := by
    simp only [differenceMultiplier,map_mul,mul_assoc]
  have hc : 2*(4*(1+(N : ℝ))^2*(q : ℝ)^3)*(q : ℝ)=
      8*(1+(N : ℝ))^2*(q : ℝ)^4 := by ring
  have he := congrArg (fun B : ℝ => 3*((integerCompactDistortion B H)^t*
    ‖compactAction (differenceCorrectionRegion_compact N q hN hq j i hs) hε t x A v‖)) hc
  exact (congrArg (fun Z : Ring => ‖compactAction hs hε t x Z v‖) ha).trans_le (ht.trans_eq he)

/-- Fully explicit growing-prime transport for the period multiplier. -/
theorem period_correction_polynomial_bound (j : Fin (q-1)) (A : Ring)
    {s : Set ℍ} (hs : IsCompact s) {ε H : ℝ} (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤1) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x (A*periodMultiplier N q hN hq j) v‖≤
      ((q : ℝ)/2)*((integerCompactDistortion (4*(1+(N : ℝ))^2*(q : ℝ)^3) H)^t*
        ‖compactAction (periodCorrectionRegion_compact N q hN hq j hs) hε t x A v‖) := by
  have ht := transported_prime_correction_bound _ q (Fact.out : q.Prime).two_le
    (defect_integer_action N q hN hq j) (by positivity) (defect_integer_height N q hq j)
    A hs hε hre him t x v
  have ha : A*periodMultiplier N q hN hq j=
      (A*symbol (defectLabel N q hN hq j))*
        Polynomial.aeval (primeX q) (QuantitativeEulerDiamondPolynomial.correctionPolynomial q) := by
    simp only [periodMultiplier,mul_assoc]
  have hc : 2*(2*(1+(N : ℝ))^2*(q : ℝ)^2)*(q : ℝ)=
      4*(1+(N : ℝ))^2*(q : ℝ)^3 := by ring
  have he := congrArg (fun B : ℝ => ((q : ℝ)/2)*((integerCompactDistortion B H)^t*
    ‖compactAction (periodCorrectionRegion_compact N q hN hq j hs) hε t x A v‖)) hc
  exact (congrArg (fun Z : Ring => ‖compactAction hs hε t x Z v‖) ha).trans_le (ht.trans_eq he)

/-- Actual averaged-row recovery with no compactness-selected multiplier
constants: the inverse contributes3, the period correction q/2, and all
remaining transport heights are explicit polynomials in q. The arithmetic
Gamma1 residuals are displayed and have not been assumed to vanish. -/
theorem prime_branch_explicit_corrections (w : ℂ) (j : Fin (q-1))
    {s : Set ℍ} (hs : IsCompact s) {ε H : ℝ} (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤1) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖(w • compact (matrixBranch N q hN hq j) hs hε t x-
      compact identityBranch hs hε t x) v‖≤
      3*‖twist N q hN (Fact.out : q.Prime).pos w (inverseRegion_compact q hs) hε t x v‖+
      ‖w‖*(∑ i : Fin (q-1),
        3*((integerCompactDistortion (8*(1+(N : ℝ))^2*(q : ℝ)^4) H)^t*
          ‖AsymptoticCongruenceDefect.operator (defectDifference N q hq i j)
            (differenceCorrectionRegion_compact N q hN hq j i hs) hε t x v‖))+
      ‖w‖*(((q : ℝ)/2)*((integerCompactDistortion (4*(1+(N : ℝ))^2*(q : ℝ)^3) H)^t*
        ‖AsymptoticCongruenceDefect.operator (defectTranslation N q hq j)
          (periodCorrectionRegion_compact N q hN hq j hs) hε t x v‖)) := by
  apply (prime_branch_averaged_bound N q hN hq w j hs hε t x v).trans
  apply add_le_add
  · apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
    apply Finset.sum_le_sum
    intro i _
    have h := difference_correction_polynomial_bound N q hN hq j i
      (symbol (integralLabel (defectDifference N q hq i j))-1) hs hε hre him t x v
    simpa only [compactAction_congruence] using h
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
    have h := period_correction_polynomial_bound N q hN hq j
      (symbol (integralLabel (defectTranslation N q hq j))-1) hs hε hre him t x v
    simpa only [compactAction_congruence] using h

#print axioms difference_correction_polynomial_bound
#print axioms period_correction_polynomial_bound
#print axioms prime_branch_explicit_corrections
end QuantitativeEulerEndpointPrepared

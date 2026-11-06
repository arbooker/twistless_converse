module

public import QuantitativeEulerDiamondRecoveryV1
public import QuantitativeEulerDiamondRegionV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeEulerDiamondDecode

open UpperHalfPlane AsymptoticCongruenceLabels AsymptoticRegularBranchFamily
open AsymptoticIntegralSubgroup
open AsymptoticFreshAveraging AsymptoticFreshCompactDefects
open QuantitativeEulerDiamondPolynomial QuantitativeArithmeticDiamondLabels QuantitativeHolomorphic
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

def primeInverse (q : ℕ) : Ring := Polynomial.aeval (primeX q) (inversePolynomial q)

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)

def differenceMultiplier (j i : Fin (q-1)) : Ring :=
  symbol (defectLabel N q hN hq j)*symbol (primeLabels q i)*primeInverse q

def periodMultiplier (j : Fin (q-1)) : Ring :=
  symbol (defectLabel N q hN hq j)*Polynomial.aeval (primeX q) (correctionPolynomial q)

theorem compact_prime_recovery_expanded (w : ℂ) (j : Fin (q-1))
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    w • compact (matrixBranch N q hN hq j) hs hε t x-compact identityBranch hs hε t x=
      compactAction hs hε t x (primeAverage N q hN hq w*primeInverse q)-
      (∑ i : Fin (q-1), w • compactAction hs hε t x
        ((symbol (integralLabel (defectDifference N q hq i j))-1)*differenceMultiplier N q hN hq j i))-
      w • compactAction hs hε t x
        ((symbol (integralLabel (defectTranslation N q hq j))-1)*periodMultiplier N q hN hq j) := by
  rw [compact_prime_recovery]
  simp only [primeCongruenceCorrection,primePeriodCorrection,primeInverse,differenceMultiplier,
    periodMultiplier,Finset.sum_mul,smul_mul_assoc,map_sum,map_smul,mul_assoc]

/-- Quantitative diamond recovery in the original observed operators.
Every region is an explicit finite union of rational images. Constants
are chosen before the sign, epsilon, cutoffs, exponent, root and vector.
All Gamma1 correction matrices are the actual arithmetic constructions. -/
theorem prime_observation_polynomial_bound (j : Fin (q-1)) :
    ∃ C₀ : ℝ, ∃ C₁ : Fin (q-1) → ℝ, ∃ C₂ : ℝ,
      1≤C₀ ∧ (∀ i, 1≤C₁ i) ∧ 1≤C₂ ∧
      ∀ (w : ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
        (H : ℝ) (_hre : ∀ z∈s, |z.re|≤1) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      ‖(w • compact (matrixBranch N q hN hq j) hs hε t x-
        compact identityBranch hs hε t x) v‖≤
      expressionMass (primeInverse q)*(integerCompactDistortion C₀ H)^t*
        ‖AsymptoticRegularObservationRows.twist N q hN (Fact.out : q.Prime).pos w
          (multiplierRegion_compact (primeInverse q) hs) hε t x v‖+
      ‖w‖*(∑ i : Fin (q-1), expressionMass (differenceMultiplier N q hN hq j i)*
        (integerCompactDistortion (C₁ i) H)^t*
        ‖AsymptoticCongruenceDefect.operator (defectDifference N q hq i j)
          (multiplierRegion_compact (differenceMultiplier N q hN hq j i) hs) hε t x v‖)+
      ‖w‖*(expressionMass (periodMultiplier N q hN hq j)*(integerCompactDistortion C₂ H)^t*
        ‖AsymptoticCongruenceDefect.operator (defectTranslation N q hq j)
          (multiplierRegion_compact (periodMultiplier N q hN hq j) hs) hε t x v‖) := by
  obtain ⟨C₀,hC₀,h₀⟩ := fixed_multiplier_region_bound (primeInverse q)
  choose C₁ hC₁ h₁ using fun i : Fin (q-1) =>
    fixed_multiplier_region_bound (differenceMultiplier N q hN hq j i)
  obtain ⟨C₂,hC₂,h₂⟩ := fixed_multiplier_region_bound (periodMultiplier N q hN hq j)
  refine ⟨C₀,C₁,C₂,hC₀,hC₁,hC₂,?_⟩
  intro w s hs ε hε H hre him t x v
  have ha := h₀ (primeAverage N q hN hq w) hs hε H hre him t x v
  rw [compactAction_primeAverage,_root_.neg_apply,norm_neg] at ha
  have hb (i : Fin (q-1)) := h₁ i (symbol (integralLabel (defectDifference N q hq i j))-1)
    hs hε H hre him t x v
  simp only [compactAction_congruence] at hb
  have hc := h₂ (symbol (integralLabel (defectTranslation N q hq j))-1) hs hε H hre him t x v
  rw [compactAction_congruence] at hc
  rw [compact_prime_recovery_expanded]
  simp only [_root_.sub_apply,_root_.sum_apply,_root_.smul_apply]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · apply (norm_sub_le _ _).trans
    apply add_le_add ha
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _)
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left hc (norm_nonneg _)

#print axioms compact_prime_recovery_expanded
#print axioms prime_observation_polynomial_bound
end QuantitativeEulerDiamondDecode

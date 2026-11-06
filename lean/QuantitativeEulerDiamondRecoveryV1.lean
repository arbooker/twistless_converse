module

public import QuantitativeEulerDiamondCompactV1
public import QuantitativeEulerDiamondActionV1
public import QuantitativeArithmeticDiamondLabelsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerDiamondDecode

open UpperHalfPlane AsymptoticIntegralSubgroup AsymptoticOrbitDecode
open AsymptoticFreshAveraging AsymptoticFreshCompactDefects
open AsymptoticCongruenceLabels AsymptoticRationalBranches AsymptoticRegularBranchFamily
open QuantitativeEulerDiamondPolynomial QuantitativeArithmeticDiamondLabels
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactBranch (cap)
open scoped Classical

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)

/-- The correction uses explicit matrices proved to belong to Gamma1(N),
with no invariance assumption on the observed vector. -/
def primeCongruenceCorrection (w : ℂ) (j : Fin (q-1)) : Ring :=
  ∑ i : Fin (q-1), w • ((symbol (integralLabel (defectDifference N q hq i j))-1)*
    symbol (defectLabel N q hN hq j)*symbol (primeLabels q i))

def primePeriodCorrection (w : ℂ) (j : Fin (q-1)) : Ring :=
  w • ((symbol (integralLabel (defectTranslation N q hq j))-1)*symbol (defectLabel N q hN hq j))

theorem finiteCorrection_eq_congruence (w : ℂ) (j : Fin (q-1)) :
    finiteCorrection (primeX q) (w • (1 : Ring))
      (symbol (defectLabel N q hN hq j)) (symbol ((defectLabel N q hN hq j)⁻¹))
      (fun i => symbol (defectLabel N q hN hq i))=primeCongruenceCorrection N q hN hq w j := by
  unfold finiteCorrection primeCongruenceCorrection
  apply Finset.sum_congr rfl
  intro i _
  rw [primeX_pow,←map_mul,defectLabel_mul_inv]
  simp only [smul_mul_assoc,one_mul]

theorem periodCorrection_eq_congruence (w : ℂ) (j : Fin (q-1)) :
    (w • (1 : Ring))*(symbol (defectLabel N q hN hq j)*(primeX q)^q*
      symbol ((defectLabel N q hN hq j)⁻¹)-1)*symbol (defectLabel N q hN hq j)=
      primePeriodCorrection N q hN hq w j := by
  rw [primeX,←map_pow,translation_fraction_period q (Fact.out : q.Prime).ne_zero,
    ←map_mul,←map_mul,defectLabel_translation_conjugate]
  simp only [primePeriodCorrection,smul_mul_assoc,one_mul]

/-- Exact recovery on the actual compact orbit space. The first term is
the observed prime average; all other defects are explicit Gamma1(N)
matrices, followed by the fixed inverse/correction polynomials. -/
theorem compact_prime_recovery (w : ℂ) (j : Fin (q-1))
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    let P := Polynomial.aeval (primeX q) (inversePolynomial q)
    let Q := Polynomial.aeval (primeX q) (correctionPolynomial q)
    w • compact (matrixBranch N q hN hq j) hs hε t x-compact identityBranch hs hε t x=
      compactAction hs hε t x (primeAverage N q hN hq w*P)-
      compactAction hs hε t x (primeCongruenceCorrection N q hN hq w j*P)-
      compactAction hs hε t x (primePeriodCorrection N q hN hq w j*Q) := by
  dsimp
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext a
  simp only [_root_.sub_apply,_root_.smul_apply,lp.coeFn_sub,Pi.sub_apply,
    lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,compact_decode,matrixBranch_label,
    identityBranch_label,one_mul,compactAction_decode]
  by_cases ha : a • x∈s
  · simp only [ite_eq_left ha]
    have h := decoded_prime_recovery N q hN hq ε t x v a w j
    dsimp at h
    rw [finiteCorrection_eq_congruence,
      periodCorrection_eq_congruence] at h
    linear_combination (cap ε t (a • x) : ℂ)*h
  · simp only [ite_eq_right ha,mul_zero,sub_self]

theorem compactAction_primeAverage (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    compactAction hs hε t x (primeAverage N q hN hq w)=
      -AsymptoticRegularObservationRows.twist N q hN (Fact.out : q.Prime).pos w hs hε t x := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext a
  simp only [_root_.neg_apply,lp.coeFn_neg,Pi.neg_apply,compactAction_decode]
  exact (primeAverage_compact_twist N q hN hq w hs hε t x v a).symm

#print axioms finiteCorrection_eq_congruence
#print axioms periodCorrection_eq_congruence
#print axioms compact_prime_recovery
#print axioms compactAction_primeAverage
end QuantitativeEulerDiamondDecode

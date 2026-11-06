module

public import QuantitativeEulerDiamondDecodeV1
public import QuantitativeEulerDiamondFiniteV1
public import AsymptoticFreshEquationV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerDiamondDecode

open UpperHalfPlane AsymptoticIntegralSubgroup AsymptoticOrbitDecode
open AsymptoticFreshAveraging QuantitativeEulerDiamondPolynomial
open AsymptoticRegularCompactBranch (Space)

def primeX (q : ℕ) : Ring := symbol (translationLabel ((q : ℚ)⁻¹))

theorem primeX_pow (q : ℕ) (i : Fin (q-1)) :
    (primeX q)^(i.val+1)=symbol (primeLabels q i) := by
  rw [primeX,←map_pow,translationLabel_pow]
  congr 2

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)

/-- The actual finite average of original prime-branch defects, indexed
by the same nonzero residues as the existing compact observation row. -/
def primeAverage (w : ℂ) : Ring :=
  ∑ i : Fin (q-1), (w • symbol (defectLabel N q hN hq i)-1)*symbol (primeLabels q i)

theorem primeAverage_eq_finiteAverage (w : ℂ) :
    primeAverage N q hN hq w=
      finiteAverage (primeX q) (w • (1 : Ring)) (fun i => symbol (defectLabel N q hN hq i)) := by
  unfold primeAverage finiteAverage
  apply Finset.sum_congr rfl
  intro i _
  rw [primeX_pow,smul_mul_assoc,one_mul]

theorem evaluate_primeAverage (ε : ℝ) (t : ℕ) (x : ℍ) (v : Space) (a : G) (w : ℂ) :
    decodedEvaluation ε t x v a (primeAverage N q hN hq w)=
      ∑ i : Fin (q-1),
        (w*decode ε t x v (defectLabel N q hN hq i*primeLabels q i*a)-
          decode ε t x v (primeLabels q i*a)) := by
  unfold primeAverage
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [sub_mul,one_mul,smul_mul_assoc,←map_mul,decodedEvaluation,map_sub,
    evaluate_smul,evaluate_symbol]

theorem evaluate_primeAverage_reflected (ε : ℝ) (t : ℕ) (x : ℍ) (v : Space) (a : G) (w : ℂ) :
    decodedEvaluation ε t x v a (primeAverage N q hN hq w)=
      w*(∑ i : Fin (q-1),decode ε t x v (reflectedLabel N q hN i*a))-
        ∑ i : Fin (q-1),decode ε t x v (primeLabels q i*a) := by
  rw [evaluate_primeAverage]
  simp_rw [defectLabel_translation N q hN hq]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum]
  congr 1
  exact congrArg (fun z : ℂ => w*z)
    (Equiv.sum_comp (AsymptoticFreshResidues.permutation q N hq)
      (fun i => decode ε t x v (reflectedLabel N q hN i*a)))

/-- Recovery of any selected original prime branch from the actual
prime average and explicit congruence corrections. Periodicity is supplied
by the decoded strip vector, and the averaging family is exactly Fin(q−1). -/
theorem decoded_prime_recovery (ε : ℝ) (t : ℕ) (x : ℍ) (v : Space) (a : G)
    (w : ℂ) (j : Fin (q-1)) :
    let g := symbol (defectLabel N q hN hq j)
    let gInv := symbol ((defectLabel N q hN hq j)⁻¹)
    let P := Polynomial.aeval (primeX q) (inversePolynomial q)
    let Q := Polynomial.aeval (primeX q) (correctionPolynomial q)
    let F := decodedEvaluation ε t x v a
    w*decode ε t x v (defectLabel N q hN hq j*a)-decode ε t x v a=
      F (primeAverage N q hN hq w*P)-
      F (finiteCorrection (primeX q) (w • (1 : Ring)) g gInv
        (fun i => symbol (defectLabel N q hN hq i))*P)-
      F ((w • (1 : Ring))*(g*(primeX q)^q*gInv-1)*g*Q) := by
  dsimp
  have hqp : 2≤q := (Fact.out : q.Prime).two_le
  have hn : q-1+1=q := by omega
  have hig : symbol ((defectLabel N q hN hq j)⁻¹) * symbol (defectLabel N q hN hq j)=1 := by
    rw [←map_mul,inv_mul_cancel,map_one]
  have h := periodic_finite_recovery (primeX q) (w • (1 : Ring))
    (symbol (defectLabel N q hN hq j)) (symbol ((defectLabel N q hN hq j)⁻¹))
    hig (by omega : 1≤q-1) (fun i => symbol (defectLabel N q hN hq i))
    (decodedEvaluation ε t x v a) (by
      rw [hn]
      exact decodedEvaluation_periodic ε t x v a q (by omega))
  rw [hn,←primeAverage_eq_finiteAverage] at h
  simpa only [smul_mul_assoc,one_mul,map_sub,decodedEvaluation,evaluate_smul,
    evaluate_symbol,evaluate_one] using h

#print axioms primeAverage_eq_finiteAverage
#print axioms evaluate_primeAverage_reflected
#print axioms decoded_prime_recovery
end QuantitativeEulerDiamondDecode

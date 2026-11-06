module

public import QuantitativeEulerDiamondPrimeRowsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerDiamondDecode

open scoped Classical

open UpperHalfPlane AsymptoticIntegralSubgroup AsymptoticOrbitDecode
open AsymptoticFreshAveraging AsymptoticFreshCompactDefects
open AsymptoticRationalBranches AsymptoticRegularBranchFamily
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactBranch (cap)

/-- The formal average in diamond recovery is precisely the existing
bounded compact prime-twist residual, including its cutoff and cap. This
is a pointwise identity on every actual orbit vector, not just its kernel. -/
theorem primeAverage_compact_twist (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)
    (w : ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) (v : Space) (a : G) :
    -(AsymptoticRegularObservationRows.twist N q hN (Fact.out : q.Prime).pos w hs hε t x v a)=
      if a • x∈s then (cap ε t (a • x) : ℂ)*
        decodedEvaluation ε t x v a (primeAverage N q hN hq w) else 0 := by
  rw [AsymptoticFreshEquation.twist_eq_sums N q hN hq]
  simp only [_root_.sub_apply,_root_.sum_apply,
    _root_.smul_apply,lp.coeFn_sub,Pi.sub_apply,lp.coeFn_smul,
    Pi.smul_apply,smul_eq_mul,lp.coeFn_sum,Finset.sum_apply,compact_decode,
    reflectedBranch_label]
  have ht (i : Fin (q-1)) :
      ofMatrix (translationBranch q i).matrix (translationBranch q i).positive=primeLabels q i := rfl
  simp_rw [ht]
  rw [evaluate_primeAverage_reflected]
  by_cases ha : a • x∈s
  · simp only [ite_eq_left ha,←Finset.mul_sum]
    ring
  · simp only [ite_eq_right ha,Finset.sum_const_zero,mul_zero,sub_self,neg_zero]

#print axioms primeAverage_compact_twist
end QuantitativeEulerDiamondDecode

module

public import QuantitativeEulerEndpointInverseV1

set_option autoImplicit false
set_option maxHeartbeats 900000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDiamondDecode QuantitativeArithmeticDiamondLabels
open AsymptoticCongruenceLabels AsymptoticFreshAveraging AsymptoticFreshCompactDefects
open AsymptoticRegularBranchFamily AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

theorem averaged_inverse_original_row_bound (N q : ℕ) [Fact q.Prime]
    (hN : 0<N) (hq : ¬q∣N) (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x (primeAverage N q hN hq w*primeInverse q) v‖≤
      3*‖twist N q hN (Fact.out : q.Prime).pos w
        (inverseRegion_compact q hs) hε t x v‖ := by
  have h := compact_prime_inverse_bound q (Fact.out : q.Prime).two_le
    (primeAverage N q hN hq w) hs hε t x v
  simpa only [compactAction_primeAverage,_root_.neg_apply,norm_neg] using h

/-- The individual original branch is recovered from its averaged q row
with uniform inverse cost three and the exact arithmetic correction terms.
The displayed congruence corrections are retained, not assumed to vanish. -/
theorem prime_branch_averaged_bound (N q : ℕ) [Fact q.Prime]
    (hN : 0<N) (hq : ¬q∣N) (w : ℂ) (j : Fin (q-1))
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖(w • compact (matrixBranch N q hN hq j) hs hε t x-
      compact identityBranch hs hε t x) v‖≤
      3*‖twist N q hN (Fact.out : q.Prime).pos w (inverseRegion_compact q hs) hε t x v‖+
      ‖w‖*(∑ i : Fin (q-1), ‖compactAction hs hε t x
        ((symbol (integralLabel (defectDifference N q hq i j))-1)*
          differenceMultiplier N q hN hq j i) v‖)+
      ‖w‖*‖compactAction hs hε t x
        ((symbol (integralLabel (defectTranslation N q hq j))-1)*
          periodMultiplier N q hN hq j) v‖ := by
  rw [compact_prime_recovery_expanded]
  simp only [_root_.sub_apply,_root_.sum_apply,_root_.smul_apply]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · apply (norm_sub_le _ _).trans
    apply add_le_add (averaged_inverse_original_row_bound N q hN hq w hs hε t x v)
    apply (norm_sum_le _ _).trans_eq
    simp only [norm_smul,Finset.mul_sum]
  · exact (norm_smul _ _).le

#print axioms averaged_inverse_original_row_bound
#print axioms prime_branch_averaged_bound
end QuantitativeEulerEndpointPrepared

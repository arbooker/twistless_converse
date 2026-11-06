module

public import QuantitativeEulerEndpointProjectiveRightV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode AsymptoticCongruenceLabels
open QuantitativeArithmeticDiamondLabels AsymptoticFreshAveraging
open AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticRegularBranchFamily AsymptoticRegularObservationRows AsymptoticFreshCompactDefects
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

/-- The two-Fricke-row estimate for a general projective right label.
Both actual composed actions carry integral representatives, with no
determinant-one requirement on those representatives. -/
theorem projective_lower_fricke_common_bound (N : ℕ) (hN : 0<N) (r : ℤ)
    (w : ℂ) (g : G) {M M' : IntegerMatrix2} {B Y H ε : ℝ}
    (hM : IntegerAction g M) (hM' : IntegerAction (integralLabel (lowerSL N r)*g) M')
    (hB : 0≤B) (hb : MatrixEntryBound M B) (hb' : MatrixEntryBound M' B) (hY : 0<Y)
    {s : Set ℍ} (hs : IsCompact s) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤1) (hlo : ∀ z∈s, Y≤z.im) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x ((symbol (integralLabel (lowerSL N r))-1)*symbol g) v‖≤
      2*((integerCompactDistortion B H)^t*
        ‖twist N 1 hN Nat.zero_lt_one w (commonImageRegion_compact B H hY) hε t x v‖) := by
  have h1 := compact_right_common_bound _ hM' hB hb' hY (frickeRow N hN w)
    hs hε hre hlo him t x v
  have h2 := compact_right_common_bound _ hM hB hb hY (frickeRow N hN w)
    hs hε hre hlo him t x v
  rw [frickeRow,compactAction_untwisted] at h1 h2
  rw [compact_lower_fricke_identity N hN r w g hs hε t x,_root_.sub_apply]
  exact ((norm_sub_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)

private theorem projective_original_sum_norm (N q : ℕ) [Fact q.Prime]
    (hN : 0<N) (hq : ¬q∣N) (j : Fin (q-1)) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x
      ((1-w • symbol (AsymptoticFreshMatrices.frickeLabel N hN))+
        (w • symbol (defectLabel N q hN hq j)-1)) v‖≤
      ‖twist N 1 hN Nat.zero_lt_one w hs hε t x v‖+
        ‖(w • compact (matrixBranch N q hN hq j) hs hε t x-compact identityBranch hs hε t x) v‖ := by
  have he := (map_add (compactAction hs hε t x)
    (1-w • symbol (AsymptoticFreshMatrices.frickeLabel N hN))
    (w • symbol (defectLabel N q hN hq j)-1)).trans
    (congrArg₂ (fun A B : Space →L[ℂ] Space => A+B)
      (compactAction_untwisted N hN w hs hε t x)
      (compact_prime_residual_eq N q hN hq j w hs hε t x))
  have h := congrArg (fun T : Space →L[ℂ] Space => ‖T v‖) he
  have triangle (A B : Space →L[ℂ] Space) : ‖(A+B) v‖≤‖A v‖+‖B v‖ := by
    simpa only [_root_.add_apply] using norm_add_le (A v) (B v)
  exact h.trans_le (triangle _ _)

/-- Canonical recovery after an arbitrary projective right label. Only
the integral representative of its composed inverse branch is estimated. -/
theorem projective_canonical_common_norm (N q : ℕ) [Fact q.Prime]
    (hN : 0<N) (hq : ¬q∣N) (j : Fin (q-1)) (w : ℂ) (hw : w*w=1)
    (g : G) {M : IntegerMatrix2} {B Y H ε : ℝ}
    (hM : IntegerAction ((defectLabel N q hN hq j)⁻¹*g) M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (hY : 0<Y)
    {s : Set ℍ} (hs : IsCompact s) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤1) (hlo : ∀ z∈s, Y≤z.im) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x
      ((symbol (integralLabel (swappedCanonical N q hq j))-1)*symbol g) v‖≤
      ‖w‖*((integerCompactDistortion B H)^t*
        (‖twist N 1 hN Nat.zero_lt_one w (commonImageRegion_compact B H hY) hε t x v‖+
          ‖(w • compact (matrixBranch N q hN hq j) (commonImageRegion_compact B H hY) hε t x-
            compact identityBranch (commonImageRegion_compact B H hY) hε t x) v‖)) := by
  let A := (1-w • symbol (AsymptoticFreshMatrices.frickeLabel N hN))+
    (w • symbol (defectLabel N q hN hq j)-1)
  have halg : (symbol (integralLabel (swappedCanonical N q hq j))-1)*symbol g=
      (-w) • (A*symbol ((defectLabel N q hN hq j)⁻¹*g)) := by
    rw [canonical_residual_identity N q hN hq w hw j,smul_mul_assoc,smul_mul_assoc,
      mul_assoc,symbol.map_mul]
  have ht := compact_right_common_bound _ hM hB hb hY A hs hε hre hlo him t x v
  have hr := projective_original_sum_norm N q hN hq j w (commonImageRegion_compact B H hY) hε t x v
  have he := congrArg (fun Z : Ring => ‖compactAction hs hε t x Z v‖) halg
  simp only [map_smul,_root_.smul_apply,norm_smul,norm_neg] at he
  exact he.trans_le (mul_le_mul_of_nonneg_left
    (ht.trans (mul_le_mul_of_nonneg_left hr (by unfold integerCompactDistortion; positivity)))
    (norm_nonneg w))

#print axioms projective_lower_fricke_common_bound
#print axioms projective_canonical_common_norm
end QuantitativeEulerEndpointPrepared

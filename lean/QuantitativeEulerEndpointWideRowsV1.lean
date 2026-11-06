module

public import QuantitativeEulerEndpointWideTransportV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeHolomorphic QuantitativeArithmetic
open QuantitativeEulerDiamondDecode QuantitativeEulerDensityGenerators
open QuantitativeArithmeticDiamondLabels AsymptoticCongruenceLabels
open AsymptoticRationalBranches AsymptoticRationalFreeness AsymptoticFreshAveraging
open AsymptoticFreshCompactDefects AsymptoticRegularBranchFamily AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

theorem compact_lower_fricke_wide_bound (N : ℕ) (hN : 0<N) (r : ℤ)
    (w : ℂ) (β : SL(2,ℤ)) {B R Y H ε : ℝ} (hB : 0≤B)
    (hb : MatrixEntryBound β.val B) (hVb : MatrixEntryBound (lowerSL N r*β).val B)
    (hY : 0<Y) {s : Set ℍ} (hs : IsCompact s) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤R) (hlo : ∀ z∈s, Y≤z.im) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖matrixCompactAction hs hε t x
      ((matrixSymbol (lowerUnipotent N r)-1)*matrixSymbol β.val) v‖≤
      2*((wideDistortion B R H)^t*
        ‖twist N 1 hN Nat.zero_lt_one w (wideImageRegion_compact B R H hY) hε t x v‖) := by
  have hfirst := compact_right_wide_bound _ (integerAction_integralLabel (lowerSL N r*β))
    hB hVb hY (frickeRow N hN w) hs hε hre hlo him t x v
  have hsecond := compact_right_wide_bound _ (integerAction_integralLabel β)
    hB hb hY (frickeRow N hN w) hs hε hre hlo him t x v
  rw [frickeRow,compactAction_untwisted] at hfirst hsecond
  have he := compact_lower_fricke_identity N hN r w (integralLabel β) hs hε t x
  rw [←integralLabel.map_mul] at he
  change ‖matrixCompactAction hs hε t x
    ((matrixSymbol (lowerSL N r).val-1)*matrixSymbol β.val) v‖≤_
  rw [matrixCompactAction_integral_defect,he,_root_.sub_apply]
  exact ((norm_sub_le _ _).trans (add_le_add hfirst hsecond)).trans_eq (by ring)

private theorem wide_scaled_norm (γ β : SL(2,ℤ)) (c : ℂ) (A : Ring)
    (h : (symbol (integralLabel γ)-1)*symbol (integralLabel β)=c • A)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    ‖matrixCompactAction hs hε t x ((matrixSymbol γ.val-1)*matrixSymbol β.val) v‖=
      ‖c‖*‖compactAction hs hε t x A v‖ := by
  rw [matrixCompactAction_integral_defect,h,map_smul,_root_.smul_apply,norm_smul]

private theorem wide_original_sum (N q : ℕ) [Fact q.Prime]
    (hN : 0<N) (hq : ¬q∣N) (j : Fin (q-1)) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    compactAction hs hε t x
      ((1-w • symbol (AsymptoticFreshMatrices.frickeLabel N hN))+
        (w • symbol (defectLabel N q hN hq j)-1))=
      twist N 1 hN Nat.zero_lt_one w hs hε t x+
        (w • compact (matrixBranch N q hN hq j) hs hε t x-
          compact identityBranch hs hε t x) := by
  have hm := compactAction_branch hs hε t x (matrixBranch N q hN hq j)
  rw [matrixBranch_label] at hm
  have hi := compactAction_branch hs hε t x identityBranch
  rw [identityBranch_label,map_one] at hi
  have hr : compactAction hs hε t x (w • symbol (defectLabel N q hN hq j)-1)=
      w • compact (matrixBranch N q hN hq j) hs hε t x-
        compact identityBranch hs hε t x := by
    calc
      _ = w • compactAction hs hε t x (symbol (defectLabel N q hN hq j))-
          compactAction hs hε t x 1 := by rw [map_sub,map_smul]
      _ = _ := congrArg₂ (fun L R : Space →L[ℂ] Space => L-R)
        (congrArg (fun L : Space →L[ℂ] Space => w • L) hm) hi
  exact (map_add (compactAction hs hε t x) _ _).trans
    (congrArg₂ (fun L R : Space →L[ℂ] Space => L+R)
      (compactAction_untwisted N hN w hs hε t x) hr)

/-- The canonical residual uses the same rectangle as all Fricke rows,
for arbitrary source width and a common integral height bound. -/
theorem canonical_wide_original_norm (N q : ℕ) [Fact q.Prime]
    (hN : 0<N) (hq : ¬q∣N) (j : Fin (q-1)) (w : ℂ) (hw : w*w=1)
    (β : SL(2,ℤ)) {M : IntegerMatrix2} {B R Y H ε : ℝ}
    (hM : IntegerAction ((defectLabel N q hN hq j)⁻¹*integralLabel β) M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (hY : 0<Y)
    {s : Set ℍ} (hs : IsCompact s) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤R) (hlo : ∀ z∈s, Y≤z.im) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖matrixCompactAction hs hε t x
      ((matrixSymbol (swappedCanonical N q hq j).val-1)*matrixSymbol β.val) v‖≤
      ‖w‖*((wideDistortion B R H)^t*
        (‖twist N 1 hN Nat.zero_lt_one w (wideImageRegion_compact B R H hY) hε t x v‖+
          ‖(w • compact (matrixBranch N q hN hq j) (wideImageRegion_compact B R H hY) hε t x-
            compact identityBranch (wideImageRegion_compact B R H hY) hε t x) v‖)) := by
  let A : Ring := (1-w • symbol (AsymptoticFreshMatrices.frickeLabel N hN))+
    (w • symbol (defectLabel N q hN hq j)-1)
  have halg : (symbol (integralLabel (swappedCanonical N q hq j))-1)*symbol (integralLabel β)=
      (-w) • (A*symbol ((defectLabel N q hN hq j)⁻¹*integralLabel β)) := by
    rw [canonical_residual_identity N q hN hq w hw j,smul_mul_assoc,smul_mul_assoc,
      mul_assoc,symbol.map_mul]
  have ht := compact_right_wide_bound _ hM hB hb hY A hs hε hre hlo him t x v
  have he : compactAction (wideImageRegion_compact B R H hY) hε t x A=
      twist N 1 hN Nat.zero_lt_one w (wideImageRegion_compact B R H hY) hε t x+
        (w • compact (matrixBranch N q hN hq j) (wideImageRegion_compact B R H hY) hε t x-
          compact identityBranch (wideImageRegion_compact B R H hY) hε t x) := by
    exact wide_original_sum N q hN hq j w (wideImageRegion_compact B R H hY) hε t x
  have hnorm := congrArg (fun T : Space →L[ℂ] Space => ‖T v‖) he
  have htri (L R : Space →L[ℂ] Space) : ‖(L+R) v‖≤‖L v‖+‖R v‖ := by
    simpa only [_root_.add_apply] using norm_add_le (L v) (R v)
  have hr := hnorm.trans_le (htri _ _)
  have hscl := wide_scaled_norm (swappedCanonical N q hq j) β (-w)
    (A*symbol ((defectLabel N q hN hq j)⁻¹*integralLabel β)) halg hs hε t x v
  have hscl' := hscl.trans (congrArg (fun c : ℝ =>
    c*‖compactAction hs hε t x (A*symbol ((defectLabel N q hN hq j)⁻¹*integralLabel β)) v‖) (norm_neg w))
  exact hscl'.trans_le (mul_le_mul_of_nonneg_left
    (ht.trans (mul_le_mul_of_nonneg_left hr (by unfold wideDistortion; positivity)))
    (norm_nonneg w))

#print axioms compact_right_wide_bound
#print axioms compact_lower_fricke_wide_bound
#print axioms canonical_wide_original_norm
end QuantitativeEulerEndpointPrepared

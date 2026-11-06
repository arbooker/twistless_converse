module

public import QuantitativeEulerEndpointCanonicalNormV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators AsymptoticCongruenceLabels
open QuantitativeEulerDiamondDecode QuantitativeArithmeticDiamondLabels
open AsymptoticFreshMatrices AsymptoticRegularObservationRows AsymptoticRegularBranchFamily
open AsymptoticFreshAveraging AsymptoticFreshCompactDefects
open AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticRegularCompactBranch (Space)
open scoped MatrixGroups Classical

private theorem matrix_compact_scaled_norm (γ β : SL(2,ℤ)) (c : ℂ) (A : Ring)
    (h : (symbol (integralLabel γ)-1)*symbol (integralLabel β)=c • A)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    ‖matrixCompactAction hs hε t x ((matrixSymbol γ.val-1)*matrixSymbol β.val) v‖=
      ‖c‖*‖compactAction hs hε t x A v‖ := by
  rw [matrixCompactAction_integral_defect,h,map_smul,_root_.smul_apply,norm_smul]

/-- The right multiplier is composed BEFORE the compact norm is estimated.
Thus the unit-strip hypothesis is used only on the original region; no
false unit-strip assertion is made about an intermediate translated image.
The bound consists of the original q=1 row and original prime branch row. -/
theorem canonical_multiplied_original_norm (N q : ℕ) [Fact q.Prime]
    (hN : 0<N) (hq : ¬q∣N) (j : Fin (q-1)) (w : ℂ) (hw : w*w=1)
    (β : SL(2,ℤ)) {B C H ε : ℝ} (hB : 0≤B) (hC : 0≤C)
    (hcan : MatrixEntryBound (swappedCanonical N q hq j).val B)
    (hβ : MatrixEntryBound β.val C) {s : Set ℍ} (hs : IsCompact s) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤1) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    let b := symbolBranch ((defectLabel N q hN hq j)⁻¹*integralLabel β)
    let hu := branchImage_compact b hs
    ‖matrixCompactAction hs hε t x
      ((matrixSymbol (swappedCanonical N q hq j).val-1)*matrixSymbol β.val) v‖≤
      ‖w‖*(integerCompactDistortion (4*(1+(N : ℝ))*B*C) H)^t*
        (‖twist N 1 hN Nat.zero_lt_one w hu hε t x v‖+
          ‖(w • compact (matrixBranch N q hN hq j) hu hε t x-
            compact identityBranch hu hε t x) v‖) := by
  let b := symbolBranch ((defectLabel N q hN hq j)⁻¹*integralLabel β)
  let A : Ring := (1-w • symbol (frickeLabel N hN))+
    (w • symbol (defectLabel N q hN hq j)-1)
  have halg : (symbol (integralLabel (swappedCanonical N q hq j))-1)*symbol (integralLabel β)=
      (-w) • (A*symbol ((defectLabel N q hN hq j)⁻¹*integralLabel β)) := by
    rw [canonical_residual_identity N q hN hq w hw j,smul_mul_assoc,smul_mul_assoc,
      mul_assoc,symbol.map_mul]
  obtain ⟨hM,hbound⟩ := inverse_prime_branch_integer_bound N q hN hq j hcan
  have hMb : IntegerAction (ofMatrix b.matrix b.positive)
      (((integralFrickeMatrix N).adjugate*(swappedCanonical N q hq j).val)*β.val) := by
    rw [symbolBranch_label]
    exact hM.mul (integerAction_integralLabel β)
  have hprod := matrix_entry_bound_mul (by positivity) hbound hβ
  have hprod' : MatrixEntryBound
      (((integralFrickeMatrix N).adjugate*(swappedCanonical N q hq j).val)*β.val)
      (4*(1+(N : ℝ))*B*C) := by
    convert hprod using 1
    ring
  have ht := compactAction_mul_symbol_integer_norm b hs hMb (by positivity) hprod'
    hε hre him t x A v
  have hm := compactAction_branch (branchImage_compact b hs) hε t x (matrixBranch N q hN hq j)
  rw [matrixBranch_label] at hm
  have hi := compactAction_branch (branchImage_compact b hs) hε t x identityBranch
  rw [identityBranch_label,map_one] at hi
  have hsum : compactAction (branchImage_compact b hs) hε t x A=
      twist N 1 hN Nat.zero_lt_one w (branchImage_compact b hs) hε t x+
        (w • compact (matrixBranch N q hN hq j) (branchImage_compact b hs) hε t x-
          compact identityBranch (branchImage_compact b hs) hε t x) := by
    dsimp [A]
    rw [map_add,compactAction_untwisted,map_sub,map_smul,hm,hi]
  have hlabel : ofMatrix b.matrix b.positive=(defectLabel N q hN hq j)⁻¹*integralLabel β :=
    symbolBranch_label _
  have heval := congrArg (fun g : G => ‖compactAction hs hε t x (A*symbol g) v‖) hlabel
  have htransport := heval.symm.trans_le ht
  have hrow : ‖compactAction (branchImage_compact b hs) hε t x A v‖≤
      ‖twist N 1 hN Nat.zero_lt_one w (branchImage_compact b hs) hε t x v‖+
      ‖(w • compact (matrixBranch N q hN hq j) (branchImage_compact b hs) hε t x-
        compact identityBranch (branchImage_compact b hs) hε t x) v‖ := by
    have htriangle (L R : Space →L[ℂ] Space) : ‖(L+R) v‖≤‖L v‖+‖R v‖ := by
      simpa only [_root_.add_apply] using norm_add_le (L v) (R v)
    exact (congrArg (fun T : Space →L[ℂ] Space => ‖T v‖) hsum).trans_le (htriangle _ _)
  have heq := matrix_compact_scaled_norm (swappedCanonical N q hq j) β (-w)
    (A*symbol ((defectLabel N q hN hq j)⁻¹*integralLabel β)) halg hs hε t x v
  have heq' := heq.trans (congrArg
    (fun c : ℝ => c*‖compactAction hs hε t x
      (A*symbol ((defectLabel N q hN hq j)⁻¹*integralLabel β)) v‖) (norm_neg w))
  have hd : 0≤(integerCompactDistortion (4*(1+(N : ℝ))*B*C) H)^t := by
    unfold integerCompactDistortion
    positivity
  have hh := mul_le_mul_of_nonneg_left hrow hd
  have htotal := htransport.trans hh
  have hscaled := mul_le_mul_of_nonneg_left htotal (norm_nonneg w)
  have hfinal := heq'.trans_le hscaled
  exact hfinal.trans_eq (mul_assoc _ _ _).symm

#print axioms canonical_multiplied_original_norm
end QuantitativeEulerEndpointPrepared

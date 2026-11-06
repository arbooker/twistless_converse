module

public import QuantitativeEulerEndpointRightRowsV1
public import QuantitativeEulerEndpointWideRowsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeHolomorphic QuantitativeArithmetic
open QuantitativeEulerDiamondDecode QuantitativeEulerDensityGenerators
open QuantitativeArithmeticDiamondLabels AsymptoticCongruenceLabels
open AsymptoticFreshAveraging AsymptoticFreshCompactDefects
open AsymptoticRegularBranchFamily AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

/-- Fixed right multiplication preserves the seven-row estimate after
composing all integral representatives before transport. -/
theorem compact_prime_wide_right_rows_of_height {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (i : Option (Generator N)) {d : ℤ} {q : ℕ} [Fact q.Prime]
    (cert : PolynomialPrimeCertificate
      (P.Q a) (P.B a i) N (P.c a i) (P.D a i) d q P.K) (hqN : ¬q∣N)
    (β : SL(2,ℤ)) {B : ℝ} (hB : 0≤B) (hβ : MatrixEntryBound β.val B)
    (L : ℝ) (hheight : 2*(localTransportConstant P a i*(q : ℝ)^4)*B≤L) :
    ∃ j : Fin (q-1), ∀ (w : ℂ) (_hw : w*w=1)
      {s : Set ℍ} (hs : IsCompact s) {ε R Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
      (_hre : ∀ z∈s, |z.re|≤R) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
      (t : ℕ) (x : ℍ) (v : Space),
      ‖matrixCompactAction hs hε t x
        ((matrixSymbol (family N a i).val-1)*matrixSymbol β.val) v‖≤
      (wideDistortion L R H)^t*
        (7*‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (wideImageRegion_compact L R H hY) hε t x v‖+
          ‖(w • compact (matrixBranch N q (NeZero.pos N) hqN j)
              (wideImageRegion_compact L R H hY) hε t x-
            compact identityBranch (wideImageRegion_compact L R H hY) hε t x) v‖) := by
  let H₀ := preparationMatrix P a i
  let C : SL(2,ℤ) := ⟨lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*
    upperUnipotent cert.l,cert.canonical_det⟩
  let U := upperSL (-cert.l)
  have hL0 : 0≤localTransportConstant P a i*(q : ℝ)^4 :=
    mul_nonneg (localTransportConstant_pos P a i).le (by positivity)
  have hL : 0≤L := (mul_nonneg (mul_nonneg (by norm_num) hL0) hB).trans hheight
  have push (M : IntegerMatrix2) (hM : MatrixEntryBound M (localTransportConstant P a i*(q : ℝ)^4)) :
      MatrixEntryBound (M*β.val) L :=
    entry_bound_mono (matrix_entry_bound_mul hL0 hM hβ) hheight
  obtain ⟨j,hj,hfirstB,hfirstVB,⟨M,hM,hMB⟩,h0B,hrB,hFB,hnB⟩ :=
    certificate_common_heights P a i cert hqN
  have hfirstB := push _ hfirstB
  have hfirstVB' : MatrixEntryBound (lowerSL N 1*((C*U)*β)).val L := by
    have hh := push _ hfirstVB
    change MatrixEntryBound ((lowerSL N 1).val*((C.val*U.val)*β.val)) L
    rw [←mul_assoc]
    exact hh
  have hMB := push _ hMB
  have hM' : IntegerAction
      ((defectLabel N q (NeZero.pos N) hqN j)⁻¹*integralLabel (U*β)) (M*β.val) := by
    simpa only [integralLabel.map_mul,mul_assoc] using hM.mul (integerAction_integralLabel β)
  have h0B := push _ h0B
  have hrB' : MatrixEntryBound (lowerSL N cert.r*(H₀*β)).val L := by
    change MatrixEntryBound ((lowerSL N cert.r).val*(H₀.val*β.val)) L
    rw [←mul_assoc]
    exact push _ hrB
  have hFB := push _ hFB
  have hnB' : MatrixEntryBound (lowerSL N (P.n a i)*(family N a i*β)).val L := by
    change MatrixEntryBound ((lowerSL N (P.n a i)).val*((family N a i).val*β.val)) L
    rw [←mul_assoc]
    exact push _ hnB
  refine ⟨j,?_⟩
  intro w hw s hs ε R Y H hε hY hre hlo him t x v
  have hwNorm : ‖w‖*‖w‖=1 := by simpa only [norm_mul,norm_one] using congrArg norm hw
  have hw1 : ‖w‖=1 := by nlinarith [norm_nonneg w]
  have hfirst := compact_lower_fricke_wide_bound N (NeZero.pos N) 1 w ((C*U)*β)
    hL hfirstB hfirstVB' hY hs hε hre hlo him t x v
  change ‖matrixCompactAction hs hε t x
    ((matrixSymbol (lowerUnipotent N 1)-1)*matrixSymbol (C.val*U.val*β.val)) v‖≤_ at hfirst
  simp only [matrixSymbol_mul,←mul_assoc] at hfirst
  have hsecond := canonical_wide_original_norm N q (NeZero.pos N) hqN j w hw (U*β)
    hM' hL hMB hY hs hε hre hlo him t x v
  rw [hw1,one_mul] at hsecond
  have hleft := congrArg (fun γ : SL(2,ℤ) =>
    ‖matrixCompactAction hs hε t x ((matrixSymbol γ.val-1)*matrixSymbol (U*β).val) v‖) hj
  have hsecond' := hleft.trans_le hsecond
  have hthird := compact_lower_fricke_wide_bound N (NeZero.pos N) cert.r w (H₀*β)
    hL h0B hrB' hY hs hε hre hlo him t x v
  have hfourth := compact_lower_fricke_wide_bound N (NeZero.pos N) (P.n a i) w (family N a i*β)
    hL hFB hnB' hY hs hε hre hlo him t x v
  have heq := congrArg (fun T : Space →L[ℂ] Space => T v)
    (compact_prime_right_defect P a i cert β hs hε t x)
  change ‖matrixCompactAction hs hε t x
    ((matrixSymbol C.val-1)*matrixSymbol (U.val*β.val)) v‖≤_ at hsecond'
  rw [matrixSymbol_mul U.val β.val,←mul_assoc] at hsecond'
  change ‖matrixCompactAction hs hε t x
    ((matrixSymbol (lowerUnipotent N cert.r)-1)*matrixSymbol (H₀.val*β.val)) v‖≤_ at hthird
  rw [matrixSymbol_mul H₀.val β.val,←mul_assoc] at hthird
  change ‖matrixCompactAction hs hε t x
    ((matrixSymbol (lowerUnipotent N (P.n a i))-1)*matrixSymbol ((family N a i).val*β.val)) v‖≤_ at hfourth
  rw [matrixSymbol_mul (family N a i).val β.val,←mul_assoc] at hfourth
  rw [heq,_root_.sub_apply,_root_.sub_apply,_root_.add_apply]
  have htriangle (u v w z : Space) : ‖u+v-w-z‖≤‖u‖+‖v‖+‖w‖+‖z‖ := by
    calc
      _ ≤ ‖u+v-w‖+‖z‖ := norm_sub_le _ _
      _ ≤ (‖u+v‖+‖w‖)+‖z‖ := add_le_add (norm_sub_le (u+v) w) le_rfl
      _ ≤ _ := add_le_add (add_le_add (norm_add_le u v) le_rfl) le_rfl
  exact ((htriangle _ _ _ _).trans
    (add_le_add (add_le_add (add_le_add hfirst hsecond') hthird) hfourth)).trans_eq (by ring)

#print axioms compact_prime_wide_right_rows_of_height
end QuantitativeEulerEndpointPrepared

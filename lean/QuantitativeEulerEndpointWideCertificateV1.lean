module

public import QuantitativeEulerEndpointWideRowsV1
public import QuantitativeEulerEndpointCommonHeightV1

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

/-- The actual prepared-generator defect is controlled on ONE explicit
common rectangle, from an arbitrary-width source, by seven copies of the q=1 row and one individual prime
row. Its integral transport height is C(P,a,i) q^4, with C independent
of q and of every certificate choice. -/
theorem compact_prime_wide_rows_of_height {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (i : Option (Generator N)) {d : ℤ} {q : ℕ} [Fact q.Prime]
    (cert : PolynomialPrimeCertificate
      (P.Q a) (P.B a i) N (P.c a i) (P.D a i) d q P.K) (hqN : ¬q∣N)
    (L : ℝ) (hheight : localTransportConstant P a i*(q : ℝ)^4≤L) :
    ∃ j : Fin (q-1), ∀ (w : ℂ) (_hw : w*w=1)
      {s : Set ℍ} (hs : IsCompact s) {ε R Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
      (_hre : ∀ z∈s, |z.re|≤R) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
      (t : ℕ) (x : ℍ) (v : Space),
      ‖(matrixCompactAction hs hε t x (matrixSymbol (family N a i).val)-
        matrixCompactAction hs hε t x 1) v‖≤
      (wideDistortion L R H)^t*
        (7*‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (wideImageRegion_compact L R H hY) hε t x v‖+
          ‖(w • compact (matrixBranch N q (NeZero.pos N) hqN j)
              (wideImageRegion_compact L R H hY) hε t x-
            compact identityBranch (wideImageRegion_compact L R H hY) hε t x) v‖) := by
  let H₀ := preparationMatrix P a i
  let C : SL(2,ℤ) := ⟨lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*
    upperUnipotent cert.l,cert.canonical_det⟩
  let U := upperSL (-cert.l)
  have hL : 0≤L := (mul_nonneg (localTransportConstant_pos P a i).le (by positivity)).trans hheight
  obtain ⟨j,hj,hfirstB,hfirstVB,⟨M,hM,hMB⟩,h0B,hrB,hFB,hnB⟩ :=
    certificate_common_heights P a i cert hqN
  have hfirstB := entry_bound_mono hfirstB hheight
  have hfirstVB := entry_bound_mono hfirstVB hheight
  have hMB := entry_bound_mono hMB hheight
  have h0B := entry_bound_mono h0B hheight
  have hrB := entry_bound_mono hrB hheight
  have hFB := entry_bound_mono hFB hheight
  have hnB := entry_bound_mono hnB hheight
  refine ⟨j,?_⟩
  intro w hw s hs ε R Y H hε hY hre hlo him t x v
  have hwNorm : ‖w‖*‖w‖=1 := by simpa only [norm_mul,norm_one] using congrArg norm hw
  have hw1 : ‖w‖=1 := by nlinarith [norm_nonneg w]
  have hfirst := compact_lower_fricke_wide_bound N (NeZero.pos N) 1 w (C*U)
    hL hfirstB hfirstVB hY hs hε hre hlo him t x v
  change ‖matrixCompactAction hs hε t x
    ((matrixSymbol (lowerUnipotent N 1)-1)*matrixSymbol (C.val*U.val)) v‖≤_ at hfirst
  rw [matrixSymbol_mul,←mul_assoc] at hfirst
  have hsecond := canonical_wide_original_norm N q (NeZero.pos N) hqN j w hw U
    hM hL hMB hY hs hε hre hlo him t x v
  rw [hw1,one_mul] at hsecond
  have hleft := congrArg (fun γ : SL(2,ℤ) =>
    ‖matrixCompactAction hs hε t x ((matrixSymbol γ.val-1)*matrixSymbol U.val) v‖) hj
  have hsecond' := hleft.trans_le hsecond
  have hthird := compact_lower_fricke_wide_bound N (NeZero.pos N) cert.r w H₀
    hL h0B hrB hY hs hε hre hlo him t x v
  have hfourth := compact_lower_fricke_wide_bound N (NeZero.pos N) (P.n a i) w (family N a i)
    hL hFB hnB hY hs hε hre hlo him t x v
  have heq := congrArg (fun T : Space →L[ℂ] Space => T v)
    (P.compact_prime_defect a i cert hs hε t x)
  rw [heq,_root_.sub_apply,_root_.sub_apply,_root_.add_apply]
  have htriangle (u v w z : Space) : ‖u+v-w-z‖≤‖u‖+‖v‖+‖w‖+‖z‖ := by
    calc
      _ ≤ ‖u+v-w‖+‖z‖ := norm_sub_le _ _
      _ ≤ (‖u+v‖+‖w‖)+‖z‖ := add_le_add (norm_sub_le (u+v) w) le_rfl
      _ ≤ _ := add_le_add (add_le_add (norm_add_le u v) le_rfl) le_rfl
  exact ((htriangle _ _ _ _).trans
    (add_le_add (add_le_add (add_le_add hfirst hsecond') hthird) hfourth)).trans_eq (by ring)

#print axioms compact_prime_wide_rows_of_height
end QuantitativeEulerEndpointPrepared
